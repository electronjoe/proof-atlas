"""Build and check a declaration against a separately authored Lean proposition."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from check_lean import select_lake, run


def lake_json(lake, arguments, root, env, stdin=None):
    result = subprocess.run([*lake, *arguments], cwd=root, env=env, input=stdin,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise ValueError(result.stderr.decode("utf-8", errors="replace").strip() or "Lake query failed")
    return [json.loads(line) for line in result.stdout.decode("utf-8-sig").splitlines()]


def hash_paths(root, paths):
    return {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sorted(paths)}


def import_headers(lake, paths, root, env):
    # The compiler parses module, public/meta imports, quoted names and comments.
    rows = lake_json(lake, ["env", "lean", "--deps-json", "--stdin"], root, env,
                     ("\n".join(paths) + "\n").encode())
    if len(rows) != 1 or len(rows[0]["imports"]) != len(paths):
        raise ValueError("Incomplete Lean import headers")
    imports = set()
    for item in rows[0]["imports"]:
        if item["errors"]:
            raise ValueError("Lean could not read an import header")
        imports.update(imp["module"] for imp in item["result"]["imports"])
    return imports


def statement_paths(root, statements):
    files = set()
    for name in statements:
        path = (root/name).resolve(strict=True)
        if not path.is_relative_to(root):
            raise ValueError(f"Statement path outside the package: {name}")
        found = sorted(path.rglob("*.lean")) if path.is_dir() else [path]
        files.update(p.relative_to(root).as_posix() for p in found if p.suffix == ".lean")
    return files


def strip_lean_comments_and_strings(text):
    """Blank Lean comments, strings, char literals and guillemet identifiers, preserving line numbers."""
    out = []
    i, n = 0, len(text)
    depth = 0

    def is_ident(ch):
        return ch.isalnum() or ch in "_'"

    while i < n:
        if depth:
            if text[i:i+2] == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif text[i:i+2] == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            elif text[i] == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue
        if text[i:i+2] == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif text[i:i+2] == "--":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
        elif text[i] == "«":
            out.append(" ")
            i += 1
            while i < n and text[i] != "»":
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            if i < n:
                out.append(" ")
                i += 1
        elif text[i] == "r" and (i == 0 or not is_ident(text[i-1])):
            j = i + 1
            while j < n and text[j] == "#":
                j += 1
            if j < n and text[j] == '"':
                hashes = j - (i + 1)
                closing = '"' + "#" * hashes
                out.append('""')
                i = j + 1
                while i < n and text[i:i+len(closing)] != closing:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
                if i < n:
                    i += len(closing)
                continue
            out.append(text[i])
            i += 1
        elif text[i] == '"':
            out.append('"')
            i += 1
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    out.append("\n" if text[i+1] == "\n" else "  ")
                    i += 2
                elif text[i] == '"':
                    out.append('"')
                    i += 1
                    break
                elif text[i] == "\n":
                    out.append("\n")
                    i += 1
                else:
                    out.append(" ")
                    i += 1
        elif text[i] == "'" and (i == 0 or not is_ident(text[i-1])):
            if text[i+1:i+2] == "\\":
                j = i + 2
                while j < n and text[j] not in "'\n" and j - i <= 8:
                    j += 1
                if j < n and text[j] == "'":
                    out.append(" " * (j - i + 1))
                    i = j + 1
                    continue
            elif i + 2 < n and text[i+1] != "\n" and text[i+2] == "'":
                out.append("   ")
                i += 3
                continue
            out.append("'")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


_ATTR_BLOCK = re.compile(r"(?:@|\battribute\s+)\[([^\]]*)\]", re.S)
_BANNED_ATTR = re.compile(r"\b(implemented_by|extern|csimp)\b")
_UNSAFE_KW = re.compile(r"\bunsafe\b")
_EVAL_CMD = re.compile(r"#eval\b")
_RUN_CMD = re.compile(r"(?m)^\s*(?:(?:local|scoped|private)\s+)*run_cmd\b")
_METAPROG_CMD = re.compile(r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|local|scoped)\s+)*(elab_rules|elab|macro_rules|macro)\b")
_FIXITY_CMD = re.compile(
    r'(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|local|scoped)\s+)*(infixl|infixr|infix|prefix|postfix)'
    r'(?:\s*\([^)]*\))*\s*:\s*\S+(?:\s*\([^)]*\))*\s*"'
)
_NOTATION_CMD = re.compile(
    r'(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|local|scoped)\s+)*notation\b'
    r'(?=(?:[^\n]*"|[^\n]*=>|\s*:\s*\S+\s*"|\s*\([^)]*\)))'
)


def scan_lean_hygiene(root, lean_paths, statement_files=()):
    """Scan audited Lean files for metaprogramming escape hatches and custom notation in Statements/."""
    stmt_set = set(statement_files)
    findings = []
    for rel in sorted(lean_paths):
        cleaned = strip_lean_comments_and_strings((root / rel).read_text(encoding="utf-8-sig"))

        def add(pos, directive, reason):
            line = cleaned.count("\n", 0, pos) + 1
            findings.append((rel, line, directive, reason))

        for m in _ATTR_BLOCK.finditer(cleaned):
            for attr in _BANNED_ATTR.finditer(m.group(1)):
                add(m.start(1) + attr.start(), f"@[{attr.group(1)}]", "escape-hatch attribute")
        for m in _UNSAFE_KW.finditer(cleaned):
            add(m.start(), "unsafe", "unsafe declaration or section")
        for m in _EVAL_CMD.finditer(cleaned):
            add(m.start(), "#eval", "compile-time evaluation command")
        for m in _RUN_CMD.finditer(cleaned):
            add(m.start(), "run_cmd", "compile-time metaprogramming command")
        for m in _METAPROG_CMD.finditer(cleaned):
            add(m.start(1), m.group(1), "custom elaborator or macro")
        if rel in stmt_set:
            for m in _FIXITY_CMD.finditer(cleaned):
                add(m.start(1), m.group(1), "custom notation in Statements/")
            for m in _NOTATION_CMD.finditer(cleaned):
                add(m.start(), "notation", "custom notation in Statements/")
    if findings:
        details = "; ".join(f"{rel}:{line}: {directive} ({reason})" for rel, line, directive, reason in findings)
        raise ValueError(f"Disallowed Lean directive in audited sources: {details}")
    return dict(checked=True, statements_checked=bool(stmt_set))


def count_lean_loc(root, lean_paths):
    """Count non-empty, non-comment Lean lines of code across audited local .lean files."""
    total = 0
    for rel in sorted(lean_paths):
        if not rel.endswith(".lean"):
            continue
        cleaned = strip_lean_comments_and_strings((root / rel).read_text(encoding="utf-8-sig"))
        total += sum(1 for line in cleaned.splitlines() if line.strip())
    return total


def _pure_external_prelude(lake, root, env):
    """Verify that a root Prelude.lean module imports only external libraries."""
    if not (root / "Prelude.lean").is_file():
        return False
    imports = import_headers(lake, ["Prelude.lean"], root, env)
    local_imports = [m for m in sorted(imports) if (root / ("/".join(m.split(".")) + ".lean")).is_file()]
    if local_imports:
        raise ValueError(
            "Prelude.lean imports local modules (" + ", ".join(local_imports)
            + "); keep Prelude.lean restricted to external/Mathlib imports"
        )
    return True


def check_routine(lake, root, env, routine_paths=(), checked_files=()):
    """Keep Routine/ glue disjoint from Statements/, Proofs/, and other local libraries.

    Routine modules may import external libraries (e.g. Mathlib), a pure-external
    Prelude.lean, and other Routine modules—never Statements/ or Proofs/.
    """
    files = statement_paths(root, routine_paths) if routine_paths else set()
    for rel in checked_files:
        if rel == "Routine.lean" or rel.startswith("Routine/"):
            files.add(rel)
    if not files:
        return []
    modules = {f[:-5].replace("/", "."): f for f in files}
    ordered = sorted(files)
    rows = lake_json(lake, ["env", "lean", "--deps-json", "--stdin"], root, env, ("\n".join(ordered) + "\n").encode())
    if len(rows) != 1 or len(rows[0]["imports"]) != len(ordered):
        raise ValueError("Incomplete Lean import headers for the routine modules")
    prelude_ok = None
    for path, item in zip(ordered, rows[0]["imports"]):
        if item["errors"]:
            raise ValueError(f"Lean could not read the imports of {path}")
        for imp in item["result"]["imports"]:
            name = imp["module"]
            source = "/".join(name.split(".")) + ".lean"
            if name in modules or not (root / source).is_file():
                continue
            if name == "Prelude":
                if prelude_ok is None:
                    prelude_ok = _pure_external_prelude(lake, root, env)
                if prelude_ok:
                    continue
            raise ValueError(
                f"Routine module {path} imports {name} ({source}), which is outside Routine/. "
                "Keep Routine/ restricted to external/Mathlib imports, Prelude, and other Routine/ modules"
            )
    return sorted(modules)


def check_statements(lake, root, env, contract, expected, statements, assumes=()):
    """Keep the expected proposition and its definitions apart from the proofs.

    `statements` lists directories or files of the package holding the paper's
    statements and definitions. Each of those modules may import only statement
    modules, a pure-external Prelude.lean, and external libraries, and the expected
    proposition (plus any --assumes propositions) must be defined in one of them.
    Lean resolves every constant from imports, so nothing the statement mentions
    can then come from a proof module or from the contract file."""
    files = statement_paths(root, statements)
    if not files:
        raise ValueError("No Lean files in the statement paths: " + ", ".join(statements))
    modules = {f[:-5].replace("/", "."): f for f in files}
    ordered = sorted(files)
    rows = lake_json(lake, ["env", "lean", "--deps-json", "--stdin"], root, env, ("\n".join(ordered) + "\n").encode())
    if len(rows) != 1 or len(rows[0]["imports"]) != len(ordered):
        raise ValueError("Incomplete Lean import headers for the statement modules")
    prelude_ok = None
    for path, item in zip(ordered, rows[0]["imports"]):
        if item["errors"]:
            raise ValueError(f"Lean could not read the imports of {path}")
        for imp in item["result"]["imports"]:
            name = imp["module"]
            source = "/".join(name.split(".")) + ".lean"
            if name not in modules and (root/source).is_file():
                if name == "Prelude":
                    if prelude_ok is None:
                        prelude_ok = _pure_external_prelude(lake, root, env)
                    if prelude_ok:
                        continue
                raise ValueError(f"Statement module {path} imports {name} ({source}), which is not a statement "
                                 f"module. Move the definitions it needs into {', '.join(statements)}")
    to_check = [expected, *assumes]
    query = ("import Lean\n" + (root/contract).read_text(encoding="utf-8-sig") + "\n" +
             "#eval show Lean.CoreM Unit from do\n  let env ← Lean.getEnv\n" +
             f"  for nameStr in ({json.dumps(to_check)} : List String) do\n" +
             "    let n := nameStr.toName\n" +
             "    IO.println s!\"PROOF-ATLAS-MODULE {nameStr} {(env.getModuleIdxFor? n).map (env.allImportedModuleNames[·]!)}\"\n")
    result = subprocess.run([*lake, "env", "lean", "--stdin"], input=query.encode(), cwd=root, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = result.stdout.decode("utf-8-sig", errors="replace")
    found = re.findall(r"^PROOF-ATLAS-MODULE (\S+) (none|\(some (\S+)\))\r?$", output, re.M)
    if result.returncode or len(found) != len(to_check):
        raise ValueError("Could not locate the expected proposition:\n" + output)
    by_name = {prop: mod for prop, _, mod in found}
    for idx, prop in enumerate(to_check):
        if prop not in by_name:
            raise ValueError(f"Could not locate proposition {prop}:\n" + output)
        module = by_name[prop]
        if module not in modules:
            where = (f"the contract {contract}" if not module else
                     f"{module} ({'/'.join(module.split('.'))}.lean)" if (root/("/".join(module.split(".")) + ".lean")).is_file()
                     else f"the external module {module}")
            role = "expected" if idx == 0 else "assumed"
            raise ValueError(f"The {role} proposition {prop} is defined in {where}, which is not a statement module. "
                             f"Define it in {', '.join(statements)}")
    return sorted(modules)


def module_inputs(lake, root, env, targets, contract):
    # Only use module-to-path correspondence for ordinary root-source Lake packages.
    # Executable/custom Lake configurations can read arbitrary files.
    import tomllib
    if (root/"lakefile.lean").exists():
        raise ValueError("Executable Lake configuration")
    config = tomllib.loads((root/"lakefile.toml").read_text(encoding="utf-8-sig"))
    if set(config) - {"name", "version", "defaultTargets", "lean_lib", "require"}:
        raise ValueError("Custom Lake package configuration")
    libraries = config["lean_lib"]
    if any(set(lib) != {"name"} for lib in libraries):
        raise ValueError("Custom Lean library configuration")
    if any(lib["name"] in targets and (root/Path(*lib["name"].split("."))).is_dir() for lib in libraries):
        raise ValueError("Requested target includes a library of modules")
    manifest = json.loads((root/"lake-manifest.json").read_bytes())
    if (manifest.get("packagesDir") != ".lake/packages" or
        any(p["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", p["rev"]) for p in manifest["packages"])):
        raise ValueError("Nonstandard dependency directory or unpinned external package")
    if any(env.get(name) for name in ("LEAN_PATH", "LEAN_SRC_PATH")):
        raise ValueError("Custom Lean search path")

    def source(name):
        if not re.fullmatch(r"[\w']+(?:\.[\w']+)*", name):
            raise ValueError("Unrecognized Lean module name")
        return "/".join(name.split(".")) + ".lean"

    contract_imports = import_headers(lake, [contract], root, env) - {"Init"}
    roots = sorted(set(targets) | contract_imports)
    # transImports recursively parses current sources through Lake's module resolver,
    # including modules reached through pinned dependencies. It does not read old .ileans.
    deps = lake_json(lake, ["query", "--json", *["+" + name + ":transImports" for name in roots]], root, env)
    if len(deps) != len(roots) or not all(isinstance(row, list) for row in deps):
        raise ValueError("Incomplete Lake transitive import metadata")
    modules = set(roots).union(*deps)
    local = {name: source(name) for name in modules if (root/source(name)).is_file()}
    if not set(targets) <= local.keys() or (root/"Init.lean").exists():
        raise ValueError("Unresolved local module target or shadowed prelude")
    # Cross-check the paths and detect local imports unknown to Lake (e.g. a stale
    # .olean outside all configured libraries). Such a graph cannot be scoped safely.
    resolved = lake_json(lake, ["query", "--json", *["+" + name + ":lean" for name in sorted(local)]], root, env)
    expected = [(root/local[name]).resolve() for name in sorted(local)]
    if ([Path(p).resolve() for p in resolved] != expected or
        any(not p.is_relative_to(root) for p in expected)):
        raise ValueError("Lake resolved a different source directory")
    headers = import_headers(lake, sorted(set(local.values())), root, env)
    if any(name not in local and (root/source(name)).is_file() for name in headers):
        raise ValueError("Local compiler import missing from Lake closure")
    return ({contract, "lean-toolchain", "lakefile.toml", "lake-manifest.json", *local.values()},
            ["+" + name for name in sorted(contract_imports)])


# Lists the package's own constants that the expected proposition unfolds to. A theorem
# contributes only its statement, so editing a proof leaves the digest unchanged. Binder
# names and metadata are erased, so reformatting or moving source leaves it unchanged too.
STATEMENT_QUERY = r'''
partial def proofAtlasCanon : Lean.Expr → Lean.Expr
  | .app f a => .app (proofAtlasCanon f) (proofAtlasCanon a)
  | .lam _ t b i => .lam `x (proofAtlasCanon t) (proofAtlasCanon b) i
  | .forallE _ t b i => .forallE `x (proofAtlasCanon t) (proofAtlasCanon b) i
  | .letE _ t v b d => .letE `x (proofAtlasCanon t) (proofAtlasCanon v) (proofAtlasCanon b) d
  | .mdata _ e => proofAtlasCanon e
  | .proj s i e => .proj s i (proofAtlasCanon e)
  | e => e

partial def proofAtlasNumeral : Lean.Expr → Bool
  | .mdata _ e => proofAtlasNumeral e
  | .lit (.natVal n) => n != 0
  | e => e.isAppOfArity ``OfNat.ofNat 3 && proofAtlasNumeral e.appFn!.appArg!

-- Applications of a default-value constant, with the type for ℕ subtraction, division and inverse.
partial def proofAtlasDefaults (heads : Lean.NameSet) (e : Lean.Expr) (acc : Array (Lean.Name × Option Lean.Expr)) :
    Array (Lean.Name × Option Lean.Expr) :=
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let acc := args.foldl (fun acc a => proofAtlasDefaults heads a acc) (if f.isConst then acc else proofAtlasDefaults heads f acc)
    match f with
    | .const n _ =>
      if !heads.contains n then acc
      else if n == ``HSub.hSub then
        if args[0]?.any (·.consumeMData.isConstOf ``Nat) then acc.push (n, args[0]?) else acc
      else if n == ``HDiv.hDiv || n == ``Inv.inv then
        -- A nonzero numeral denominator, as in `1/2`, cannot take the default.
        if (if n == ``HDiv.hDiv then args[5]? else args[2]?).any proofAtlasNumeral then acc else acc.push (n, args[0]?)
      else acc.push (n, none)
    | _ => acc
  | .const n _ => if heads.contains n && n != ``HSub.hSub then acc.push (n, none) else acc
  | .lam _ t b _ | .forallE _ t b _ => proofAtlasDefaults heads b (proofAtlasDefaults heads t acc)
  | .letE _ t v b _ => proofAtlasDefaults heads b (proofAtlasDefaults heads v (proofAtlasDefaults heads t acc))
  | .mdata _ e | .proj _ _ e => proofAtlasDefaults heads e acc
  | _ => acc

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let local_ : Lean.NameSet := (__LOCAL__ : List String).foldl (fun s m => s.insert m.toName) {}
  let heads : Lean.NameSet := (__DEFAULTS__ : List String).foldl (fun s m => s.insert m.toName) {}
  let ppNoNot (e : Lean.Expr) : Lean.CoreM String := do
    let opts := (← Lean.getOptions).setBool `pp.notation false
    Lean.withOptions (fun _ => opts) do
      return toString (← (Lean.Meta.ppExpr e).run')
  let mut todo := #[(__ROOT__ : String).toName]
  let mut seen : Lean.NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "unknown constant {n}"
    let mod := (env.getModuleIdxFor? n).map (env.allImportedModuleNames[·]!)
    unless mod.all local_.contains do continue
    let value := if ci.isTheorem then none else ci.value? (allowOpaque := true)
    let (kind, next) : String × Array Lean.Name := match ci with
      | .inductInfo v => ("inductive", v.ctors.toArray)
      | .ctorInfo v => ("constructor", #[v.induct])
      | .defnInfo _ => ("def", #[]) | .thmInfo _ => ("theorem", #[]) | .opaqueInfo _ => ("opaque", #[])
      | .axiomInfo _ => ("axiom", #[]) | .recInfo _ => ("recursor", #[]) | .quotInfo _ => ("quot", #[])
    todo := todo ++ ci.type.getUsedConstants ++ (value.map (·.getUsedConstants)).getD #[] ++ next
    let range ← Lean.findDeclarationRanges? n
    let text := s!"{kind} {ci.levelParams} : {proofAtlasCanon ci.type}" ++
      (value.map (s!" := {proofAtlasCanon ·}")).getD ""
    let ppType ← ppNoNot ci.type
    let ppVal ← value.mapM ppNoNot
    let ppNoNotation := ppType ++ (ppVal.map (s!" := {·}")).getD ""
    let noncomp := Lean.isNoncomputable env n
    let mut uses : Array Lean.Json := #[]
    for (c, t) in proofAtlasDefaults heads ci.type ((value.map (proofAtlasDefaults heads · #[])).getD #[]) do
      let mut ty := []
      if let some t := t then
        let s ← if t.hasLooseBVars then pure "a bound type" else toString <$> (Lean.Meta.ppExpr t).run'
        ty := [("type", Lean.Json.str s)]
      uses := uses.push (Lean.Json.mkObj ([("construct", Lean.Json.str (toString c))] ++ ty))
    IO.println <| "PROOF-ATLAS-CONSTANT " ++ (Lean.Json.mkObj [("name", toString n),
      ("module", Lean.toJson (mod.map toString)), ("canonical", text), ("defaults", Lean.Json.arr uses),
      ("noncomputable", Lean.toJson noncomp), ("pp_no_notation", Lean.Json.str ppNoNotation),
      ("lines", Lean.toJson (range.map fun r => #[r.range.pos.line, r.range.endPos.line]))]).compress
'''

# Lean makes every function total. Each of these returns a default value (usually 0) where the
# mathematical object is undefined, so a statement built on one can be true and mean nothing.
DEFAULT_VALUES = {
    "HDiv.hDiv": "x / 0 = 0", "Inv.inv": "0⁻¹ = 0",
    "Ring.inverse": "0 when not a unit (e.g., singular matrix or non-invertible element)",
    "Matrix.inv": "singular matrix A⁻¹ evaluates to a default (0) when det A is not a unit",
    "HSub.hSub": "a − b = 0 when b > a", "Nat.sub": "a − b = 0 when b > a", "Nat.pred": "pred 0 = 0",
    "Real.log": "log 0 = 0, log x = log |x|", "Real.logb": "logb b 0 = 0, logb b x = logb b |x|, 0 when log b = 0",
    "Real.sqrt": "√x = 0 for x < 0",
    "ENNReal.toReal": "⊤.toReal = 0 (infinite values, expectations, or ∫⁻ integrals map silently to 0)",
    "ENNReal.toNNReal": "⊤.toNNReal = 0 (infinite values map silently to 0)",
    "ENNReal.ofReal": "ofReal x = 0 when x ≤ 0",
    "InfSet.sInf": "sInf ∅ = 0 in ℝ and ℕ; 0 in ℝ when unbounded below",
    "SupSet.sSup": "sSup ∅ = 0 in ℝ; 0 when unbounded above",
    "iInf": "as sInf of the range: 0 in ℝ when empty or unbounded below",
    "iSup": "as sSup of the range: 0 in ℝ when empty or unbounded above",
    # Recent Mathlib names it Filter.limUnder; older pins, limUnder.
    "Filter.limUnder": "an arbitrary value when the limit does not exist",
    "limUnder": "an arbitrary value when the limit does not exist", "tsum": "0 when not summable",
    "MeasureTheory.integral": "0 when not integrable", "intervalIntegral": "0 when not integrable on the interval",
    "MeasureTheory.condExp": "0 when not integrable or on non-σ-finite measures",
    "deriv": "0 when not differentiable", "derivWithin": "0 when not differentiable within the set",
    "fderiv": "0 when not differentiable",
    "Function.invFun": "an arbitrary value when the argument is not in the range of f",
}


def default_meaning(use):
    ty = use.get("type", "")
    if use["construct"] == "HDiv.hDiv" and ty in ("ℕ", "ℤ", "Nat", "Int"):
        return "x / 0 = 0, and division rounds down"
    if use["construct"] == "Inv.inv" and (ty == "Matrix" or ty.startswith("Matrix ") or ty.startswith("(Matrix ")):
        return "singular matrix A⁻¹ evaluates to a default (0) when det A is not a unit"
    return DEFAULT_VALUES.get(use["construct"], "")


STD_MATHLIB_PACKAGES = {
    "mathlib", "std", "batteries", "aesop", "qq", "cli",
    "proofwidgets", "importgraph", "plausible", "leansearchclient", "checkdecls",
}
KNOWN_UPSTREAM_ORGS = re.compile(
    r"^https?://github\.com/(?:leanprover|leanprover-community)/"
    r"|^https?://github\.com/Siddhartha-Gadgil/LeanSearchClient(?:\.git)?/?$",
    re.I,
)


def external_packages(root):
    """List pinned external packages from lake-manifest.json, flagging non-Mathlib third-party repos."""
    manifest = json.loads((root / "lake-manifest.json").read_bytes())
    direct_names = set()
    toml_path = root / "lakefile.toml"
    if toml_path.is_file():
        import tomllib
        try:
            config = tomllib.loads(toml_path.read_text(encoding="utf-8-sig"))
            for req in config.get("require", []):
                if isinstance(req, dict) and isinstance(req.get("name"), str):
                    direct_names.add(req["name"])
        except (OSError, ValueError):
            pass
    result = []
    for pkg in sorted(manifest.get("packages", []), key=lambda item: item.get("name", "").casefold()):
        name = pkg.get("name", "")
        inherited = bool(pkg.get("inherited", False))
        direct = (name in direct_names) if direct_names else (not inherited)
        url = pkg.get("url", "")
        rev = pkg.get("rev", "")
        official = name.casefold() in STD_MATHLIB_PACKAGES and (not url or bool(KNOWN_UPSTREAM_ORGS.match(url)))
        entry = dict(name=name, rev=rev, direct=direct, third_party=not official)
        if url:
            entry["url"] = url
        result.append(entry)
    return result


def axiom_profile(axioms):
    """Human-readable summary of a declaration's standard Lean axiom profile."""
    if not axioms:
        return "Constructive (0 axioms)"
    ordered = sorted(axioms)
    if "Classical.choice" in ordered:
        return "Standard classical axioms (" + ", ".join(ordered) + ")"
    return "Standard Lean axioms (" + ", ".join(ordered) + ")"


def statement_record(lake, root, env, contract, expected):
    """Hash the expected proposition and every definition of this package it unfolds to.

    Also returns the default-value uses in those definitions and statements. They are
    outside the digest: they follow from the hashed constants."""
    modules = {}
    for path in inputs(root):
        if path.endswith(".lean"):
            modules[path[:-5].replace("/", ".")] = path
    program = ("import Lean\n" + (root/contract).read_text(encoding="utf-8-sig") + "\n" +
               STATEMENT_QUERY.replace("__LOCAL__", json.dumps(sorted(modules))).replace("__ROOT__", json.dumps(expected))
               .replace("__DEFAULTS__", json.dumps(sorted(DEFAULT_VALUES))))
    result = subprocess.run([*lake, "env", "lean", "--stdin"], input=program.encode(),
                            cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = result.stdout.decode("utf-8-sig", errors="replace")
    rows = [json.loads(line.split(" ", 1)[1]) for line in output.splitlines()
            if line.startswith("PROOF-ATLAS-CONSTANT ")]
    if result.returncode or not rows or rows[0]["name"] != expected:
        raise ValueError("Could not list the definitions behind the expected statement:\n" + output)
    constants = sorted((dict(name=row["name"], file=modules.get(row["module"], contract), lines=row["lines"],
                             sha256=hashlib.sha256(row["canonical"].encode()).hexdigest(),
                             noncomputable=bool(row.get("noncomputable", False)),
                             pp_no_notation=row.get("pp_no_notation", "")) for row in rows),
                       key=lambda c: c["name"])
    digest = hashlib.sha256("".join(f'{c["name"]} {c["sha256"]}\n' for c in constants).encode()).hexdigest()
    found = {(row["name"], use["construct"], use.get("type", "")): row for row in rows for use in row["defaults"]}
    defaults = [dict(constant=name, file=modules.get(row["module"], contract), lines=row["lines"],
                     construct=construct, **({"type": ty} if ty else {}))
                for (name, construct, ty), row in sorted(found.items(), key=lambda item: item[0])]
    return dict(expected=expected, sha256=digest, constants=constants), defaults


# Derives from the expected proposition what an example must show: that its hypotheses can
# all hold at once. Every binder of the statement's ∀/→ prefix is a hypothesis. A ∀/→ inside
# the conclusion (a guarded clause, reached through ∧, ∃ and let) adds its own binders, so the
# guard must hold too. Each such path becomes `∃ x…, H₁ ∧ … ∧ Hₖ`; paths are joined with ∧.
# A variable the theorem itself chooses (under ∃) enters only when a hypothesis mentions it.
# Only the expected definition itself is unfolded, so ¬, ≠ and ⊆ stay conclusions.
HYPOTHESES_QUERY = r'''
def proofAtlasPath (ys chosen : Array Lean.Expr) : Lean.MetaM Lean.Expr := do
  let mut binders := #[]
  let mut facts := #[]
  for y in ys do
    let t ← Lean.Meta.inferType y
    let used ← ys.anyM fun z => return (← Lean.Meta.inferType z).containsFVar y.fvarId!
    if chosen.contains y then
      if used then binders := binders.push y
    else if (← Lean.Meta.isProp t) && !used then facts := facts.push t
    else binders := binders.push y
  let mut body := facts.back?.getD (Lean.mkConst ``True)
  for f in facts.pop.reverse do body := Lean.mkAnd f body
  for y in binders.reverse do body ← Lean.Meta.mkAppM ``Exists #[← Lean.Meta.mkLambdaFVars #[y] body]
  return body

partial def proofAtlasPaths (e : Lean.Expr) (xs chosen : Array Lean.Expr) : Lean.MetaM (Array Lean.Expr) := do
  match e.consumeMData with
  | .forallE n t b bi =>
    Lean.Meta.withLocalDecl n bi t fun x => do
      let found ← proofAtlasPaths (b.instantiate1 x) (xs.push x) chosen
      if found.isEmpty then return #[← proofAtlasPath (xs.push x) chosen] else return found
  | .letE _ _ v b _ => proofAtlasPaths (b.instantiate1 v) xs chosen
  | e =>
    if e.isAppOfArity ``And 2 then
      return (← proofAtlasPaths e.appFn!.appArg! xs chosen) ++ (← proofAtlasPaths e.appArg! xs chosen)
    if e.isAppOfArity ``Exists 2 then
      if let .lam n t b bi := e.appArg!.consumeMData then
        return ← Lean.Meta.withLocalDecl n bi t fun x =>
          proofAtlasPaths (b.instantiate1 x) (xs.push x) (chosen.push x)
    return #[]

#eval show Lean.MetaM Unit from do
  let env ← Lean.getEnv
  let some ci := env.find? (__EXPECTED__ : String).toName | throwError "unknown expected proposition"
  let some v := ci.value? | throwError "the expected proposition has no definition body"
  let us ← ci.levelParams.mapM fun _ => Lean.Meta.mkFreshLevelMVar
  let paths ← proofAtlasPaths (v.instantiateLevelParams ci.levelParams us) #[] #[]
  let goal := paths.pop.foldr Lean.mkAnd (paths.back?.getD (Lean.mkConst ``True))
  let wn := (__WITNESS__ : String).toName
  let w ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels wn)
  let ok ← Lean.Meta.isDefEq w goal
  let mod := (env.getModuleIdxFor? wn).map (env.allImportedModuleNames[·]!)
  let range ← Lean.findDeclarationRanges? wn
  IO.println <| "PROOF-ATLAS-HYPOTHESES " ++ (Lean.Json.mkObj [("matches", Lean.toJson ok),
    ("needed", toString (← Lean.Meta.ppExpr (← Lean.instantiateMVars goal))),
    ("proved", toString (← Lean.Meta.ppExpr (← Lean.instantiateMVars w))),
    ("module", Lean.toJson (mod.map toString)),
    ("lines", Lean.toJson (range.map fun r => #[r.range.pos.line, r.range.endPos.line]))]).compress
'''


DECL_KIND_QUERY = r'''
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let n := (__DECL__ : String).toName
  let kind := match env.find? n with
    | some (.thmInfo _) => "theorem"
    | some (.defnInfo _) => "def"
    | some (.axiomInfo _) => "axiom"
    | some (.opaqueInfo _) => "opaque"
    | some (.inductInfo _) => "inductive"
    | some (.ctorInfo _) => "constructor"
    | some (.recInfo _) => "recursor"
    | some (.quotInfo _) => "quot"
    | none => "missing"
  IO.println s!"PROOF-ATLAS-DECL-KIND {kind}"
'''


# Walks the audited proof declaration's transitive local constant closure in Lean.Environment
# (following both types and proof/definition bodies across local modules, including through
# compiler-generated auxiliaries) to extract used local theorems, .Statement dependencies,
# and reachable local definition counts.
PROOF_CLOSURE_QUERY = r'''
partial def proofAtlasIsPropType : Lean.Expr → Bool
  | .sort .zero => true
  | .forallE _ _ b _ => proofAtlasIsPropType b
  | .letE _ _ _ b _ => proofAtlasIsPropType b
  | .mdata _ e => proofAtlasIsPropType e
  | _ => false

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let local_ : Lean.NameSet := (__LOCAL__ : List String).foldl (fun s m => s.insert m.toName) {}
  let mut todo := #[(__DECL__ : String).toName]
  let mut seen : Lean.NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mod := (env.getModuleIdxFor? n).map (env.allImportedModuleNames[·]!)
    unless mod.all local_.contains do continue
    let value := ci.value? (allowOpaque := true)
    let (kind, next) : String × Array Lean.Name := match ci with
      | .inductInfo v => ("inductive", v.ctors.toArray)
      | .ctorInfo v => ("constructor", #[v.induct])
      | .defnInfo _ => ("def", #[]) | .thmInfo _ => ("theorem", #[]) | .opaqueInfo _ => ("opaque", #[])
      | .axiomInfo _ => ("axiom", #[]) | .recInfo _ => ("recursor", #[]) | .quotInfo _ => ("quot", #[])
    todo := todo ++ ci.type.getUsedConstants ++ (value.map (·.getUsedConstants)).getD #[] ++ next
    IO.println <| "PROOF-ATLAS-CLOSURE " ++ (Lean.Json.mkObj [
      ("name", toString n),
      ("kind", Lean.Json.str kind),
      ("module", Lean.toJson (mod.map toString)),
      ("is_prop", Lean.toJson (proofAtlasIsPropType ci.type))
    ]).compress
'''


_COMPILER_AUX_PART = re.compile(
    r"^(?:_proof_\d+|_?match_\d+|_sunfold|_cstage\d+|_closed_\d+|_rarg|_boxed|_aux_\d+|_uniq|"
    r"eq_\d+|casesOn|recOn|brecOn|below|ibelow|noConfusion|noConfusionType|ctorIdx|sizeOf_spec)$"
)


def is_compiler_aux(name):
    """Return True if a Lean constant name contains a compiler-generated auxiliary component."""
    return any(_COMPILER_AUX_PART.match(part) for part in str(name).split("."))


def parse_proof_closure(output, declaration, expected, statement_modules=()):
    """Parse PROOF-ATLAS-CLOSURE lines into kernel-extracted theorem/statement deps and size metrics."""
    rows = [json.loads(line.split(" ", 1)[1]) for line in output.splitlines()
            if line.startswith("PROOF-ATLAS-CLOSURE ")]
    if not rows or not any(row.get("name") == declaration for row in rows):
        raise ValueError(f"Could not extract local constant closure for {declaration}:\n" + output)
    stmt_mods = set(statement_modules or ())
    used_theorems = set()
    used_statements = set()
    local_defs = set()
    reachable_modules = set()
    seen = set()
    for row in rows:
        name = row.get("name", "")
        mod = row.get("module")
        if mod:
            reachable_modules.add(mod)
        if not name or name in seen or is_compiler_aux(name):
            continue
        seen.add(name)
        kind = row.get("kind", "")
        is_prop = bool(row.get("is_prop", False))
        if kind == "theorem" and name != declaration:
            used_theorems.add(name)
        if kind in ("def", "opaque", "inductive"):
            local_defs.add(name)
        if name != expected and kind in ("def", "opaque", "inductive", "axiom"):
            in_stmt_mod = bool(mod and (mod in stmt_mods or mod == "Statements" or mod.startswith("Statements.")))
            if name.endswith(".Statement") or (in_stmt_mod and is_prop):
                used_statements.add(name)
    ordered_theorems = sorted(used_theorems)
    ordered_statements = sorted(used_statements)
    return dict(
        used_local_theorems=ordered_theorems,
        used_local_statements=ordered_statements,
        reachable_local_defs=len(local_defs),
        reachable_local_theorems=len(ordered_theorems),
        _reachable_modules=sorted(reachable_modules),
    )


def proof_closure_record(lake, root, env, contract, declaration, expected, statement_modules=()):
    """Walk the audited declaration's transitive local constant closure in Lean.Environment."""
    modules = {path[:-5].replace("/", ".") for path in inputs(root) if path.endswith(".lean")}
    program = ("import Lean\n" + (root / contract).read_text(encoding="utf-8-sig") + "\n" +
               PROOF_CLOSURE_QUERY.replace("__LOCAL__", json.dumps(sorted(modules)))
               .replace("__DECL__", json.dumps(declaration)))
    result = subprocess.run([*lake, "env", "lean", "--stdin"], input=program.encode(),
                            cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = result.stdout.decode("utf-8-sig", errors="replace")
    if result.returncode:
        raise ValueError(f"Could not inspect transitive local constant closure for {declaration}:\n" + output)
    return parse_proof_closure(output, declaration, expected, statement_modules=statement_modules)


def expected_claim_type(expected, assumes=()):
    """Build the Lean type `A₁ → … → Aₖ → Expected` for conditional or unconditional proofs."""
    return " → ".join([*assumes, expected]) if assumes else expected


def theorem_info_report(output, declaration):
    """Verify the audited proof declaration is a kernel `.thmInfo` (`wasOriginallyTheorem`)."""
    kinds = re.findall(r"^PROOF-ATLAS-DECL-KIND (\S+)\r?$", output, re.M)
    if len(kinds) != 1:
        raise ValueError(f"Could not verify kernel declaration kind for {declaration}:\n" + output)
    if kinds[0] != "theorem":
        raise ValueError(f"Proof declaration {declaration} must be a Lean theorem (.thmInfo), found {kinds[0]}")
    return True


def axiom_report(output, declaration):
    """The axioms `#print axioms` lists for one declaration, refusing any beyond Lean's standard three."""
    quoted = re.escape("'"+declaration+"'")
    reports = re.findall(quoted + r" (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output)
    if len(reports) != 1:
        raise ValueError("Could not identify one axiom report for the requested declaration:\n"+output)
    axioms = [a.strip() for a in reports[0].split(",") if a.strip()]
    additional = set(axioms) - {"propext", "Classical.choice", "Quot.sound"}
    if additional:
        raise ValueError(f"{declaration} uses additional axioms: "+", ".join(sorted(additional)))
    return axioms


def hypotheses_record(lake, root, env, contract, expected, witness):
    """Check that `witness` proves the hypotheses of `expected` can all hold, using standard axioms."""
    modules = {path[:-5].replace("/", "."): path for path in inputs(root) if path.endswith(".lean")}
    program = ("import Lean\n" + (root/contract).read_text(encoding="utf-8-sig") + "\n" +
               HYPOTHESES_QUERY.replace("__EXPECTED__", json.dumps(expected)).replace("__WITNESS__", json.dumps(witness)) +
               f"#print axioms {witness}\n")
    result = subprocess.run([*lake, "env", "lean", "--stdin"], input=program.encode(),
                            cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = result.stdout.decode("utf-8-sig", errors="replace")
    rows = [json.loads(line.split(" ", 1)[1]) for line in output.splitlines()
            if line.startswith("PROOF-ATLAS-HYPOTHESES ")]
    if result.returncode or len(rows) != 1:
        raise ValueError("Could not check the hypotheses example:\n" + output)
    if not rows[0]["matches"]:
        raise ValueError(f"The example {witness} proves\n  {rows[0]['proved']}\nbut the hypotheses of {expected} "
                         f"need\n  {rows[0]['needed']}\nState the example with that type.")
    record = dict(declaration=witness, proposition=rows[0]["needed"], axioms=axiom_report(output, witness))
    mod = rows[0].get("module")
    witness_file = contract if mod is None else modules.get(mod)
    if witness_file and rows[0].get("lines"):
        record["file"] = witness_file
        record["lines"] = rows[0]["lines"]
    return record


def inputs(root):
    result = {}
    for directory, children, files in os.walk(root):
        children[:] = [child for child in children if not child.startswith(".")]
        for name in files:
            if name.endswith(".lean") or name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                path = Path(directory)/name
                result[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def audit(args):
    root = args.package.resolve(strict=True)
    contract = (root/args.contract).resolve(strict=True)
    if not contract.is_relative_to(root) or contract.suffix != ".lean":
        raise ValueError("Keep the independent contract in the Lean package")
    statement_only = bool(getattr(args, "statement_only", False))
    declaration = getattr(args, "declaration", None)
    witness = getattr(args, "witness", None)
    targets = list(getattr(args, "target", None) or [])
    statements = list(getattr(args, "statements", None) or [])
    routine = list(getattr(args, "routine", None) or [])
    assumes = list(getattr(args, "assumes", None) or [])
    if statement_only:
        if declaration:
            raise ValueError("--statement-only does not accept a proof declaration")
        if assumes:
            raise ValueError("--statement-only does not accept --assumes")
        if not statements:
            raise ValueError("--statement-only requires --statements")
    elif not declaration:
        raise ValueError("Supply a proof declaration, or pass --statement-only")
    for name in (*([declaration] if declaration else []), args.expected, *assumes, *targets, *([witness] if witness else [])):
        if not re.fullmatch(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", name):
            raise ValueError("Expected a fully qualified Lean identifier")
    pin = (root/"lean-toolchain").read_text(encoding="utf-8-sig").strip()
    env = os.environ.copy()
    env.update(ELAN_TOOLCHAIN=pin, GIT_ALLOW_PROTOCOL="file", MATHLIB_NO_CACHE_ON_UPDATE="1")
    if not (root/"lake-manifest.json").is_file():
        raise ValueError("Run initial package setup and keep the contract with the source files")
    lake = select_lake(root, pin, env, sys.stderr, offline=True)
    contract_path = contract.relative_to(root).as_posix()
    scoped = None
    build_targets = list(targets)
    if build_targets or statements:
        try:
            closure, contract_targets = module_inputs(lake, root, env, targets, contract_path)
        except (ImportError, KeyError, OSError, TypeError, ValueError) as exc:
            if statements:
                raise ValueError(f"Cannot verify statement independence: {exc}") from exc
            print(f"Using full-package source hashes: {exc}", file=sys.stderr)
        else:
            # A default build still hashes the whole package. Statement checks
            # need a verified module layout regardless of the build target.
            if build_targets or statement_only:
                scoped = closure
                build_targets += [t for t in contract_targets if t[1:] not in targets]
    initial = inputs(root) if scoped is None else hash_paths(root, scoped)
    if contract_path not in initial or pin != (root/"lean-toolchain").read_text(encoding="utf-8-sig").strip():
        raise ValueError("Missing contract or toolchain pin changed during audit setup")
    # Static hygiene runs before `lake build` so compile-time side effects fail before elaboration.
    stmt_files = statement_paths(root, statements) if statements else set()
    if statements and "Prelude.lean" in initial:
        stmt_files = set(stmt_files) | {"Prelude.lean"}
    hygiene = scan_lean_hygiene(root, [p for p in initial if p.endswith(".lean")], stmt_files)
    # Keep Routine/ glue isolated from Statements/ and Proofs/ before building.
    routine_modules = check_routine(lake, root, env, routine, [p for p in initial if p.endswith(".lean")])
    # The Lake build runner sends output to an actual file descriptor.
    run([*lake, "--no-cache", "build", *build_targets], root, env, sys.stderr)
    theorem_info = False
    if statement_only:
        program = (contract.read_text(encoding="utf-8-sig") + "\n" +
                   f"example : Prop := {args.expected}\n#print axioms {args.expected}\n")
        result = subprocess.run([*lake, "env", "lean", "--stdin"], input=program.encode(),
                                cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = result.stdout.decode("utf-8-sig", errors="replace")
        if result.returncode or re.search(r"\bwarning:", output, re.I):
            raise ValueError("Lean statement check did not pass cleanly:\n"+output)
        axioms = axiom_report(output, args.expected)
    else:
        claim_type = expected_claim_type(args.expected, assumes)
        program = ("import Lean\n" + contract.read_text(encoding="utf-8-sig") + "\n" +
                   f"example : {claim_type} := {declaration}\n#print axioms {declaration}\n" +
                   DECL_KIND_QUERY.replace("__DECL__", json.dumps(declaration)))
        result = subprocess.run([*lake, "env", "lean", "--stdin"], input=program.encode(),
                                cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = result.stdout.decode("utf-8-sig", errors="replace")
        if result.returncode or re.search(r"\bwarning:", output, re.I):
            raise ValueError("Lean contract check did not pass cleanly:\n"+output)
        axioms = axiom_report(output, declaration)
        theorem_info = theorem_info_report(output, declaration)
    if witness:
        hypotheses = hypotheses_record(lake, root, env, contract_path, args.expected, witness)
    else:
        hypotheses = None
        print("Warning: no --witness was given, so nothing shows that the hypotheses of the expected "
              "proposition can hold. See 'Show the hypotheses can hold' in SKILL.md.", file=sys.stderr)
    stmt_modules = []
    if statements:
        stmt_modules = check_statements(lake, root, env, contract_path, args.expected, statements, assumes=assumes)
    else:
        print("Warning: no --statements path was given, so nothing checks that the expected proposition "
              "and its definitions are independent of the proof modules. Older atlases keep working; "
              "see 'Separate statements from proofs' in SKILL.md to migrate.", file=sys.stderr)
    # A custom source layout can hide local definitions from the fingerprint.
    statement, defaults = (statement_record(lake, root, env, contract_path, args.expected)
                           if scoped or statements else (None, None))
    proof_closure = (proof_closure_record(lake, root, env, contract_path, declaration, args.expected,
                                          statement_modules=stmt_modules)
                     if (not statement_only and (scoped or statements)) else None)
    reachable_mods = proof_closure.pop("_reachable_modules", None) if proof_closure else None
    if reachable_mods:
        reachable_paths = [p for p in ("/".join(m.split(".")) + ".lean" for m in reachable_mods)
                           if p in initial]
        checked_lean_loc = count_lean_loc(root, reachable_paths or [p for p in initial if p.endswith(".lean")])
    else:
        checked_lean_loc = count_lean_loc(root, [p for p in initial if p.endswith(".lean")])
    if scoped is None:
        final = inputs(root)
    else:
        try:
            final_scope, _ = module_inputs(lake, root, env, targets, contract_path)
        except (KeyError, OSError, TypeError, ValueError) as exc:
            raise ValueError(f"Could not confirm the dependency closure after the audit: {exc}") from exc
        final = hash_paths(root, final_scope)
    if initial != final:
        raise ValueError("Package inputs changed during the audit; rerun on stable sources")
    ext_pkgs = external_packages(root)
    profile = axiom_profile(axioms)
    if statement_only:
        return dict(statement_only=True, contract=contract_path, expected=args.expected,
                    toolchain=pin, axioms=axioms, axiom_profile=profile, external_packages=ext_pkgs,
                    targets=targets, input_scope="module-closure",
                    checked_inputs=initial, checked_lean_loc=checked_lean_loc,
                    statements=statements, hygiene=hygiene,
                    lean_output=output.strip(),
                    statement=statement, defaults=defaults,
                    **({"reachable_local_defs": len(statement["constants"])} if statement else {}),
                    **({"routine": routine_modules} if routine_modules else {}),
                    **({"hypotheses": hypotheses} if hypotheses else {}))
    return dict(declaration=declaration, contract=contract_path,
                expected=args.expected, toolchain=pin, axioms=axioms, axiom_profile=profile,
                external_packages=ext_pkgs, theorem_info=theorem_info,
                targets=targets, input_scope="module-closure" if scoped is not None else "full-package",
                checked_inputs=initial, checked_lean_loc=checked_lean_loc,
                statements=statements, hygiene=hygiene,
                lean_output=output.strip(),
                **({"assumes": assumes} if assumes else {}),
                **({"routine": routine_modules} if routine_modules else {}),
                **(proof_closure if proof_closure else {}),
                **({"statement": statement, "defaults": defaults} if statement else {}),
                **({"hypotheses": hypotheses} if hypotheses else {}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("contract", help="File importing the target and defining the expected proposition")
    parser.add_argument("expected", help="Name of the independent proposition")
    parser.add_argument("declaration", nargs="?", help="Name of the proof to check (omit with --statement-only)")
    parser.add_argument("--statement-only", action="store_true",
                        help="Audit only the expected proposition, definitions, defaults and optional --witness without checking a proof")
    parser.add_argument("--target", action="append", default=[], help="Build this proof module before checking its independent contract")
    parser.add_argument("--statements", action="append", default=[],
                        help="Directory or file holding the paper's statements and definitions; they may not import proof modules")
    parser.add_argument("--routine", action="append", default=[],
                        help="Directory or file holding Routine/ glue lemmas; they may not import Statements/ or Proofs/")
    parser.add_argument("--assumes", action="append", default=[],
                        help="Expected proposition in Statements/ assumed as a hypothesis by a conditional proof (repeatable in binder order)")
    parser.add_argument("--witness", help="Declaration proving that the hypotheses of the expected proposition can all hold")
    parser.add_argument("--output", type=Path, help="New evidence file to create on success")
    args = parser.parse_args()
    try:
        if args.output and args.output.exists():
            raise FileExistsError(f"Refusing to overwrite existing evidence file: {args.output}")
        data = json.dumps(audit(args), indent=2)+"\n"
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            with args.output.open("x", encoding="utf-8") as out:
                out.write(data)
        else:
            print(data, end="")
    except (OSError, RuntimeError, ValueError) as exc:
        sys.exit(str(exc))
