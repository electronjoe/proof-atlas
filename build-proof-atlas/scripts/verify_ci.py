"""Recheck closed atlas claims on a clean GitHub runner and emit per-claim evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace

from atlas import (
    STEP_VERIFIED_PAPER_BADGE,
    STEP_VERIFIED_SUPPLIED_BADGE,
    collect_other_claim_declarations,
    generate_challenge_harness,
    lean_ci_level,
    load_bound_tex_sources,
    local,
    resolve_claim_step_map,
)
from audit_lean import (
    _pure_external_prelude,
    audit_batch,
    axiom_report,
    import_headers,
    scan_lean_hygiene,
    scan_no_sorry,
    statement_paths,
)
from check_lean import select_lake

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
PARITY_CHECKS = (
    "statements_isolation",
    "scan_lean_hygiene",
    "routine_prelude_isolation",
    "thm_info",
    "assembly_assumptions",
    "statement_sha256",
    "witness_recheck",
    "step_map_audit",
)
KNOWN_PARANOID_KERNELS = ("nanoda", "lean4lean", "con-leche")

# Cross-environment Challenge vs. Solution verifier mirroring Comparator's core check:
# loads Challenge.olean and Solution.olean into separate Lean.Environments so identical
# theorem names never collide, and confirms matching canonical types, level params, and .thmInfo.
CHALLENGE_SOLUTION_COMPARE_QUERY = r'''
import Lean

partial def proofAtlasChallengeCanon : Lean.Expr → Lean.Expr
  | .app f a => .app (proofAtlasChallengeCanon f) (proofAtlasChallengeCanon a)
  | .lam _ t b i => .lam `x (proofAtlasChallengeCanon t) (proofAtlasChallengeCanon b) i
  | .forallE _ t b i => .forallE `x (proofAtlasChallengeCanon t) (proofAtlasChallengeCanon b) i
  | .letE _ t v b d => .letE `x (proofAtlasChallengeCanon t) (proofAtlasChallengeCanon v) (proofAtlasChallengeCanon b) d
  | .mdata _ e => proofAtlasChallengeCanon e
  | .proj s i e => .proj s i (proofAtlasChallengeCanon e)
  | e => e

#eval show IO Unit from do
  Lean.initSearchPath (← Lean.findSysroot)
  let envC ← Lean.importModules #[{ module := `Challenge }] {}
  let envS ← Lean.importModules #[{ module := `Solution }] {}
  for nameStr in (__TARGETS__ : List String) do
    let n := nameStr.toName
    let some ciC := envC.find? n | throw <| IO.userError s!"Missing target in Challenge: {nameStr}"
    let some ciS := envS.find? n | throw <| IO.userError s!"Missing target in Solution: {nameStr}"
    let isThmC := match ciC with | .thmInfo _ => true | _ => false
    let isThmS := match ciS with | .thmInfo _ => true | _ => false
    if !isThmC || !isThmS then
      throw <| IO.userError s!"Target {nameStr} must be a kernel theorem (.thmInfo) in both Challenge and Solution"
    if ciC.levelParams != ciS.levelParams then
      throw <| IO.userError s!"Target {nameStr} universe level parameters differ between Challenge and Solution"
    if proofAtlasChallengeCanon ciC.type != proofAtlasChallengeCanon ciS.type then
      throw <| IO.userError s!"Target {nameStr} type differs between Challenge and Solution"
    IO.println s!"PROOF-ATLAS-HARNESS-OK {nameStr}"
'''


def parse_lean_version(toolchain):
    """Parse a pinned Lean 4 toolchain string into (major, minor, patch), or None."""
    m = re.search(r"(?:^|:|/)v?(\d+)\.(\d+)\.(\d+)\b", str(toolchain or "").strip())
    if not m:
        return None
    return (int(m.group(1)), int(m.group(2)), int(m.group(3)))


def supports_lake_paranoid(toolchain):
    """Return True if the pinned Lean toolchain supports `lake check --paranoid` (>= v4.35.0)."""
    ver = parse_lean_version(toolchain)
    return ver is not None and ver >= (4, 35, 0)


def _dedup_ordered(items):
    out = []
    for item in items:
        if item and item not in out:
            out.append(item)
    return out


def _resolve_ci_statements(package, prior, ci_level, label):
    """Enforce Statements/ isolation parity even if a local receipt omitted --statements."""
    statements = list(prior.get("statements") or [])
    if not statements:
        detected = []
        if (package / "Statements").is_dir():
            detected.append("Statements")
        elif (package / "Statements.lean").is_file():
            detected.append("Statements.lean")
        statements = detected
    if ci_level == "paranoid" and not statements:
        raise ValueError(
            f"{label}: paranoid CI requires isolated Statements/ modules (--statements Statements)"
        )
    return statements


def _resolve_ci_routine(package, prior):
    """Collect Routine/ isolation paths from the receipt and package layout."""
    routine = []
    for item in prior.get("routine") or []:
        if (package / item).exists():
            rel = item
        elif re.fullmatch(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", str(item)):
            mod_rel = "/".join(str(item).split(".")) + ".lean"
            rel = mod_rel if (package / mod_rel).is_file() else item
        else:
            rel = item
        if rel not in routine:
            routine.append(rel)
    if (package / "Routine").is_dir() and "Routine" not in routine:
        routine.append("Routine")
    if (package / "Routine.lean").is_file() and "Routine.lean" not in routine:
        routine.append("Routine.lean")
    return routine


def _package_env(package):
    pin = (package / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
    env = os.environ.copy()
    env.update(ELAN_TOOLCHAIN=pin, GIT_ALLOW_PROTOCOL="file", MATHLIB_NO_CACHE_ON_UPDATE="1")
    return pin, env


def prepare(package, contracts):
    """Materialize locked dependencies and the Mathlib modules used by the package."""
    manifest = json.loads((package / "lake-manifest.json").read_bytes())
    env = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1")
    subprocess.run(["lake", "env", "lean", "--version"], cwd=package, env=env, check=True)
    if not any(p["name"] == "mathlib" for p in manifest.get("packages", [])):
        return
    files = sorted({name for record in contracts for name in record["checked_inputs"] if name.endswith(".lean")})
    modules = sorted(m for m in import_headers(["lake"], files, package, env) if m == "Mathlib" or m.startswith("Mathlib."))
    if modules:
        subprocess.run(["lake", "exe", "cache", "get", *modules], cwd=package, env=env, check=True)


def _manifest_has_package(package, name):
    manifest_path = package / "lake-manifest.json"
    if not manifest_path.is_file():
        return False
    try:
        manifest = json.loads(manifest_path.read_bytes())
    except (OSError, ValueError):
        return False
    return any(p.get("name", "").casefold() == name.casefold() for p in manifest.get("packages", []))


def verify_challenge_solution_lean(package, pkg_harness, env, lake):
    """Verify hash-locked Challenge.lean and Solution.lean in Lean.

    Checks:
      1. Challenge.lean imports ONLY isolated Statements/ modules (never Proofs/Routine/Assembly).
      2. Statements/ and Solution.lean pass scan_lean_hygiene and contain zero `sorry`.
      3. Every target theorem in Solution.lean matches Challenge.lean's type and is a
         kernel `.thmInfo` using only standard Lean axioms (zero `sorryAx`).
      4. Every Statements/ expected proposition depends only on standard axioms (zero `sorryAx`).
    """
    stmt_files = sorted(statement_paths(package, pkg_harness["statements_paths"]))
    allowed_stmt_mods = {f[:-5].replace("/", ".") for f in stmt_files}
    challenge_imports = import_headers(lake, ["Challenge.lean"], package, env)
    for mod in sorted(challenge_imports):
        mod_rel = "/".join(mod.split(".")) + ".lean"
        if (package / mod_rel).is_file() and mod not in allowed_stmt_mods:
            raise ValueError(
                f"Challenge.lean imports local module {mod} ({mod_rel}) outside Statements/"
            )

    scan_lean_hygiene(package, ["Challenge.lean", "Solution.lean", *stmt_files], set(stmt_files))
    scan_no_sorry(package, [*stmt_files, "Solution.lean"])

    targets = pkg_harness["targets"]
    theorem_names = [t["theorem"] for t in targets]

    if pkg_harness.get("lakefile_configured"):
        for mod in ("Challenge", "Solution"):
            res = subprocess.run(
                [*lake, "--no-cache", "build", mod],
                cwd=package, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            if res.returncode:
                out = res.stdout.decode("utf-8-sig", errors="replace")
                raise ValueError(f"Failed to build {mod}.lean:\n{out}")

        cmp_program = CHALLENGE_SOLUTION_COMPARE_QUERY.replace("__TARGETS__", json.dumps(theorem_names))
        cmp_res = subprocess.run(
            [*lake, "env", "lean", "--stdin"],
            input=cmp_program.encode("utf-8"),
            cwd=package, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        cmp_out = cmp_res.stdout.decode("utf-8-sig", errors="replace")
        matched = re.findall(r"^PROOF-ATLAS-HARNESS-OK (\S+)\r?$", cmp_out, re.M)
        if cmp_res.returncode or matched != theorem_names:
            raise ValueError("Challenge/Solution kernel comparison failed:\n" + cmp_out)

        unique_expected = _dedup_ordered([t["expected"] for t in targets])
        sol_check = ["import Solution"]
        for t in targets:
            sol_check.append(f"#print axioms {t['theorem']}")
        for exp in unique_expected:
            sol_check.append(f"#print axioms _root_.{exp}")
        ax_res = subprocess.run(
            [*lake, "env", "lean", "--stdin"],
            input=("\n".join(sol_check) + "\n").encode("utf-8"),
            cwd=package, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        ax_out = ax_res.stdout.decode("utf-8-sig", errors="replace")
        if ax_res.returncode or re.search(r"\bwarning:", ax_out, re.I):
            raise ValueError("Solution.lean axiom verification failed:\n" + ax_out)
        for t in targets:
            axiom_report(ax_out, t["theorem"])
        for exp in unique_expected:
            axiom_report(ax_out, exp)
    else:
        # Standalone elaboration fallback when Challenge/Solution are not declared in lakefile.toml.
        ch_res = subprocess.run(
            [*lake, "env", "lean", "Challenge.lean"],
            cwd=package, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        if ch_res.returncode:
            out = ch_res.stdout.decode("utf-8-sig", errors="replace")
            raise ValueError("Challenge.lean failed to elaborate:\n" + out)

        unique_expected = _dedup_ordered([t["expected"] for t in targets])
        sol_src = (package / "Solution.lean").read_text(encoding="utf-8-sig")
        checks = [
            f"example : _root_.{t['expected']} := {t['theorem']}\n"
            f"#print axioms {t['theorem']}\n"
            for t in targets
        ] + [f"#print axioms _root_.{exp}\n" for exp in unique_expected]
        sol_res = subprocess.run(
            [*lake, "env", "lean", "--stdin"],
            input=(sol_src + "\n" + "".join(checks)).encode("utf-8"),
            cwd=package, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        sol_out = sol_res.stdout.decode("utf-8-sig", errors="replace")
        if sol_res.returncode or re.search(r"\bwarning:", sol_out, re.I):
            raise ValueError("Solution.lean verification failed:\n" + sol_out)
        for t in targets:
            axiom_report(sol_out, t["theorem"])
        for exp in unique_expected:
            axiom_report(sol_out, exp)

    return dict(
        verified=True,
        challenge_sha256=pkg_harness["challenge_sha256"],
        solution_sha256=pkg_harness["solution_sha256"],
        statements_sha256=pkg_harness["statements_sha256"],
        targets_checked=theorem_names,
    )


def run_comparator(package, pkg_harness, env, lake):
    """Run Lean FRO's Comparator against Challenge and Solution if installed."""
    explicit = os.environ.get("COMPARATOR_BIN")
    cmd = None
    if explicit:
        cmd = [explicit]
    elif shutil.which("comparator"):
        cmd = [shutil.which("comparator")]
    elif _manifest_has_package(package, "comparator"):
        cmd = [*lake, "exe", "comparator"]
    if not cmd:
        return None
    if not pkg_harness.get("lakefile_configured"):
        raise ValueError(
            "Comparator requires [[lean_lib]] entries for `Challenge` and `Solution` in lakefile.toml"
        )
    config = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": [t["theorem"] for t in pkg_harness["targets"]],
        "permitted_axioms": sorted(STANDARD_AXIOMS),
    }
    with tempfile.NamedTemporaryFile("w", suffix=".json", encoding="utf-8", delete=False) as cfg:
        json.dump(config, cfg, indent=2)
        cfg_path = Path(cfg.name)
    try:
        res = subprocess.run(
            [*cmd, str(cfg_path)],
            cwd=package, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
    finally:
        cfg_path.unlink(missing_ok=True)
    if res.returncode:
        out = res.stdout.decode("utf-8-sig", errors="replace")
        raise ValueError(f"Comparator verification failed (exit {res.returncode}):\n{out}")
    return ["comparator"]


def run_lean4checker(package, modules, env, lake):
    """Run `lean4checker --fresh` against built proof/Solution modules if installed."""
    explicit = os.environ.get("LEAN4CHECKER_BIN")
    if explicit:
        cmd = [*lake, "env", explicit, "--fresh", *modules]
    elif shutil.which("lean4checker"):
        cmd = [*lake, "env", shutil.which("lean4checker"), "--fresh", *modules]
    elif _manifest_has_package(package, "lean4checker"):
        cmd = [*lake, "exe", "lean4checker", "--fresh", *modules]
    else:
        return None
    res = subprocess.run(cmd, cwd=package, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if res.returncode:
        out = res.stdout.decode("utf-8-sig", errors="replace")
        raise ValueError(f"lean4checker --fresh failed (exit {res.returncode}):\n{out}")
    return ["lean4checker"]


def run_lake_paranoid(package, targets, toolchain, env, lake):
    """Run Lean >= v4.35.0 `lake check --paranoid` multi-kernel replay when supported."""
    if not supports_lake_paranoid(toolchain):
        return None
    res = subprocess.run(
        [*lake, "check", "--paranoid", *targets],
        cwd=package, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    out = res.stdout.decode("utf-8-sig", errors="replace")
    if res.returncode:
        raise ValueError(f"`lake check --paranoid` failed (exit {res.returncode}):\n{out}")
    lowered = out.casefold()
    detected = [k for k in KNOWN_PARANOID_KERNELS if re.search(rf"\b{re.escape(k)}\b", lowered)]
    return ["lake-check-paranoid", *detected]


def run_paranoid_checkers(package, pkg_harness, toolchain, proof_modules, env, lake):
    """Execute all available paranoid independent checkers; fail closed if none is available."""
    extra_kernels = []
    comp = run_comparator(package, pkg_harness, env, lake)
    if comp:
        extra_kernels.extend(comp)

    checker_modules = ["Solution"] if pkg_harness.get("lakefile_configured") else sorted(set(proof_modules))
    l4c = run_lean4checker(package, checker_modules, env, lake)
    if l4c:
        extra_kernels.extend(l4c)

    paranoid_targets = ["Solution"] if pkg_harness.get("lakefile_configured") else sorted(set(proof_modules))
    lk = run_lake_paranoid(package, paranoid_targets, toolchain, env, lake)
    if lk:
        extra_kernels.extend(lk)

    extra_kernels = _dedup_ordered(extra_kernels)
    if not extra_kernels:
        raise ValueError(
            "Paranoid CI (`hosting.lean_ci_level = \"paranoid\"`) requires at least one independent "
            "checker (Comparator, lean4checker, or Lean >= v4.35.0 `lake check --paranoid`), "
            "but none was available on this runner."
        )
    return _dedup_ordered(["lean-kernel", *extra_kernels])


def _collect_packages(root, project, ci_level):
    """Validate project.json closures and group closed claims by Lean package."""
    materials = json.loads(local(root, project["reader"]).read_text(encoding="utf-8-sig")) if project.get("reader") else {}
    notes = materials.get("claims", {})
    tex_sources = None

    def get_tex_sources():
        nonlocal tex_sources
        if tex_sources is None:
            tex_sources = load_bound_tex_sources(root, project)
        return tex_sources

    packages = {}
    for label, work in project.get("work", {}).items():
        status = work.get("status")
        if status == "conditional":
            closure = work.get("closure")
            if closure and closure.get("audit"):
                prior = json.loads(local(root, closure["audit"]).read_bytes())
                if not prior.get("assumes") or not work.get("assumes"):
                    raise ValueError(
                        f"{label}: conditional claim must record non-empty assumes in both project.json and its audit receipt"
                    )
            continue
        if status != "closed":
            continue
        closure = work.get("closure") or {}
        if not closure.get("audit") or not closure.get("package"):
            raise ValueError(f"{label}: closed claim is missing closure.audit or closure.package")
        raw = local(root, closure["audit"]).read_bytes()
        prior = json.loads(raw)
        package = local(root, closure["package"])
        if prior.get("statement_only"):
            raise ValueError(f"{label}: closed claim cannot use a --statement-only receipt")
        if any(part.get("status") != "checked" for part in work.get("subproofs", [])):
            raise ValueError(f"{label}: closed claim has unchecked subproofs")
        if prior.get("assumes") or work.get("assumes"):
            raise ValueError(f"{label}: closed claim cannot carry unresolved conditional assumptions")
        if not prior.get("checked_inputs"):
            raise ValueError(f"{label}: local receipt has no checked_inputs")
        if any(
            not local(package, f).is_file() or hashlib.sha256(local(package, f).read_bytes()).hexdigest() != h
            for f, h in prior["checked_inputs"].items()
        ):
            raise ValueError(f"{label}: recorded source hashes differ from the checkout")
        rel_pkg = package.relative_to(root)
        expected_work_inputs = {(rel_pkg / f).as_posix(): h for f, h in prior["checked_inputs"].items()}
        if work.get("checked_inputs") != expected_work_inputs:
            raise ValueError(f"{label}: project.json checked_inputs differ from the local audit receipt")
        if any(closure.get(key) != prior.get(key) for key in ("declaration", "expected")):
            raise ValueError(f"{label}: local certificate names differ from the closure")
        asm_spec = work.get("assembly") or {}
        if asm_spec.get("expected") and asm_spec["expected"] != closure["expected"]:
            raise ValueError(f"{label}: assembly expected proposition differs from closure.expected")
        if asm_spec.get("witness"):
            prior_witness = (prior.get("hypotheses") or {}).get("declaration")
            if prior_witness != asm_spec["witness"]:
                raise ValueError(
                    f"{label}: local receipt witness ({prior_witness}) does not match declared assembly witness ({asm_spec['witness']})"
                )
        note = notes.get(label, {})
        has_raw_step_map = (
            work.get("step_map") is not None
            or asm_spec.get("step_map") is not None
            or note.get("step_map") is not None
        )
        step_map_info = None
        if has_raw_step_map:
            default_main = asm_spec.get("declaration") or closure["declaration"]
            step_map_info = resolve_claim_step_map(
                root, label, work, note, get_tex_sources(), default_main=default_main,
            )
            if prior.get("step_audit"):
                if prior["step_audit"].get("verified") is not True:
                    raise ValueError(f"{label}: local receipt has unverified step_audit")
                if prior["step_audit"].get("step_map_sha256") != step_map_info["step_map_sha256"]:
                    raise ValueError(
                        f"{label}: step_map changed since the local audit receipt; rerun audit_lean.py --step-map"
                    )
        elif prior.get("step_audit"):
            prior_sa = prior["step_audit"]
            if prior_sa.get("verified") is not True:
                raise ValueError(f"{label}: local receipt has unverified step_audit")
            raw_steps = prior_sa.get("steps") or []
            if not raw_steps or any(s.get("origin") != "supplied" for s in raw_steps):
                raise ValueError(
                    f"{label}: local receipt has step_audit, but no step_map is configured on work[{label}] "
                    "or reader.json to verify verbatim TeX provenance of paper steps"
                )
            step_map_info = dict(
                source=None,
                main_declaration=prior_sa.get("main_declaration") or prior["declaration"],
                main_deps=prior_sa.get("main_deps_declared"),
                forbidden_mains=list(prior_sa.get("forbidden_mains") or []),
                step_map_sha256=prior_sa["step_map_sha256"],
                steps=[
                    dict(id=s["id"], lemma=s["lemma"], step_deps=list(s.get("declared_deps") or []), origin="supplied")
                    for s in raw_steps
                ],
                paper_step_count=0,
                supplied_step_count=len(raw_steps),
            )
        statements = _resolve_ci_statements(package, prior, ci_level, label)
        routine = _resolve_ci_routine(package, prior)
        packages.setdefault(package, []).append(
            (label, work, prior, hashlib.sha256(raw).hexdigest(), statements, routine, step_map_info)
        )
    return packages


def _verify_git_and_hosting(root, project):
    repository = os.environ["GITHUB_REPOSITORY"]
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    if commit != os.environ["GITHUB_SHA"] or project["hosting"]["repository"].casefold() != ("https://github.com/" + repository).casefold():
        raise ValueError("Checkout differs from the requested GitHub revision or repository")
    if project["hosting"].get("lean_ci") != "enabled":
        raise ValueError("GitHub Lean verification is not enabled for this project")
    return repository, commit


def prepare_project(root, *, level=None):
    """Fetch locked dependencies and Mathlib caches for all packages with closed claims."""
    project = json.loads((root / "project.json").read_bytes())
    _verify_git_and_hosting(root, project)
    ci_level = level or lean_ci_level(project)
    packages = _collect_packages(root, project, ci_level)
    for package, group in packages.items():
        prepare(package, [prior for _, _, prior, _, _, _, _ in group])
    return sorted(p.relative_to(root).as_posix() for p in packages)


def install_paranoid_tools(root, bin_dir):
    """Build and install `lean4checker` matching the project's pinned Lean toolchains into `bin_dir`."""
    project = json.loads((root / "project.json").read_bytes())
    _verify_git_and_hosting(root, project)
    packages = _collect_packages(root, project, "paranoid")
    toolchains = sorted({
        (pkg / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
        for pkg in packages if (pkg / "lean-toolchain").is_file()
    })
    bin_dir = Path(bin_dir).resolve()
    bin_dir.mkdir(parents=True, exist_ok=True)
    installed = []
    for pin in toolchains:
        if supports_lake_paranoid(pin):
            print(f"Toolchain {pin} supports built-in `lake check --paranoid`.", flush=True)
            continue
        m = re.search(r"(v\d+\.\d+\.\d+(?:-[A-Za-z0-9.]+)?)$", pin)
        if not m:
            continue
        tag = m.group(1)
        if shutil.which("lean4checker") or (bin_dir / "lean4checker").is_file():
            continue
        with tempfile.TemporaryDirectory() as tmp:
            clone_dir = Path(tmp) / "lean4checker"
            subprocess.run(
                ["git", "clone", "--depth", "1", "--branch", tag,
                 "https://github.com/leanprover/lean4checker.git", str(clone_dir)],
                check=True,
            )
            env = dict(os.environ, ELAN_TOOLCHAIN=pin)
            subprocess.run(["lake", "build", "lean4checker"], cwd=clone_dir, env=env, check=True)
            built = clone_dir / ".lake/build/bin/lean4checker"
            if not built.is_file():
                raise ValueError(f"lean4checker binary was not produced at {built}")
            dest = bin_dir / "lean4checker"
            shutil.copy2(built, dest)
            installed.append(str(dest))
    return installed


def verify(root, *, offline=False, level=None):
    """Recheck every closed claim with full local audit_lean.py invariant parity and optional paranoid replay."""
    project = json.loads((root / "project.json").read_bytes())
    repository, commit = _verify_git_and_hosting(root, project)
    ci_level = level or lean_ci_level(project)
    if ci_level not in ("standard", "paranoid"):
        raise ValueError("ci_level must be 'standard' or 'paranoid'")

    result = dict(
        repository=repository,
        commit=commit,
        run_id=int(os.environ["GITHUB_RUN_ID"]),
        attempt=int(os.environ["GITHUB_RUN_ATTEMPT"]),
        ci_level=ci_level,
        kernels_checked=["lean-kernel"],
        checks_enforced=list(PARITY_CHECKS),
        claims={},
    )
    if os.environ.get("PROOF_ATLAS_NETWORK_ISOLATED"):
        result["network_isolated"] = True

    packages = _collect_packages(root, project, ci_level)
    all_kernels = ["lean-kernel"]
    challenge_harnesses = {}

    for package, group in packages.items():
        if not offline:
            prepare(package, [prior for _, _, prior, _, _, _, _ in group])
        pin, pkg_env = _package_env(package)
        lake = select_lake(package, pin, pkg_env, sys.stderr, offline=True)
        # Always enforce Prelude.lean pure-external isolation when Prelude.lean exists in the package.
        if (package / "Prelude.lean").is_file():
            _pure_external_prelude(lake, package, pkg_env)

        pkg_claim_records = {}
        pkg_proof_modules = []
        batch_items = []
        batch_specs = []

        for label, work, prior, digest, statements, routine, step_map_info in group:
            print(f"Rechecking {label} ({prior['declaration']})", flush=True)
            targets = prior.get("targets")
            if not targets:
                imports = import_headers(lake, [prior["contract"]], package, pkg_env)
                targets = sorted(m for m in imports if (package / (m.replace(".", "/") + ".lean")).is_file())
            witness = (prior.get("hypotheses") or {}).get("declaration")
            step_map_arg = None
            if step_map_info is not None:
                other_decls = collect_other_claim_declarations(project, label)
                merged_forbidden = _dedup_ordered([*step_map_info["forbidden_mains"], *other_decls])
                step_map_arg = dict(
                    main_declaration=step_map_info["main_declaration"] or prior["declaration"],
                    main_deps=step_map_info["main_deps"],
                    forbidden_mains=merged_forbidden,
                    steps=[
                        {k: v for k, v in s.items() if k in ("id", "lemma", "step_deps", "origin")}
                        for s in step_map_info["steps"]
                    ],
                )
            batch_items.append((label, work, prior, digest, statements, routine, targets, step_map_info))
            batch_specs.append(SimpleNamespace(
                package=package,
                contract=prior["contract"],
                target=targets,
                expected=prior["expected"],
                declaration=prior["declaration"],
                statements=statements,
                routine=routine,
                assumes=[],
                witness=witness,
                step_map=step_map_arg,
            ))

        checked_list = audit_batch(package, batch_specs, lake=lake, env=pkg_env)
        if len(checked_list) != len(batch_items):
            raise ValueError(
                f"Batched audit returned {len(checked_list)} receipts for {len(batch_items)} claims"
            )

        for (label, work, prior, digest, statements, routine, targets, step_map_info), checked in zip(batch_items, checked_list):
            # Full invariant parity assertions against local audit_lean.py guarantees.
            if not checked.get("theorem_info"):
                raise ValueError(f"{label}: audited declaration is not a kernel theorem (.thmInfo)")
            hygiene = checked.get("hygiene") or {}
            if not hygiene.get("checked") or (statements and not hygiene.get("statements_checked")):
                raise ValueError(f"{label}: static Lean hygiene check did not cover all required sources")
            if statements and checked.get("statements") != statements:
                raise ValueError(f"{label}: Statements/ isolation check mismatch")
            if checked.get("assumes"):
                raise ValueError(f"{label}: closed claim cannot carry unresolved conditional assumptions")
            if checked["declaration"].startswith("Assembly.") and "Assembly.lean" not in checked.get("checked_inputs", {}):
                raise ValueError(f"{label}: Assembly declaration is missing Assembly.lean from checked_inputs")
            if set(checked["axioms"]) - STANDARD_AXIOMS:
                raise ValueError(f"{label}: non-standard axioms detected in CI")
            if set(checked["axioms"]) != set(prior["axioms"]):
                raise ValueError(f"{label}: CI axiom profile differs from local receipt")

            # Verify no hidden imported file was omitted from the local receipt's checked_inputs.
            for fname, fhash in checked["checked_inputs"].items():
                if fname in prior["checked_inputs"] and prior["checked_inputs"][fname] != fhash:
                    raise ValueError(f"{label}: input hash mismatch for {fname}")
            if prior.get("input_scope") == checked.get("input_scope"):
                extra_inputs = sorted(set(checked["checked_inputs"]) - set(prior["checked_inputs"]))
                if extra_inputs:
                    raise ValueError(
                        f"{label}: CI dependency closure contains inputs absent from local receipt: {', '.join(extra_inputs)}"
                    )

            fingerprint = (checked.get("statement") or {}).get("sha256")
            if statements and not fingerprint:
                raise ValueError(f"{label}: missing statement.sha256 binding for isolated statement")
            if prior.get("statement") and fingerprint != prior["statement"]["sha256"]:
                raise ValueError(f"{label}: statement fingerprint differs from the local receipt")

            if prior.get("hypotheses"):
                chk_hyp = checked.get("hypotheses")
                if (not chk_hyp
                        or chk_hyp.get("declaration") != prior["hypotheses"].get("declaration")
                        or chk_hyp.get("proposition") != prior["hypotheses"].get("proposition")
                        or (set(chk_hyp.get("axioms", [])) - STANDARD_AXIOMS)):
                    raise ValueError(f"{label}: witness re-check differs from the local receipt")

            step_meta = {}
            if step_map_info is not None or prior.get("step_audit"):
                chk_sa = checked.get("step_audit")
                if not chk_sa or chk_sa.get("verified") is not True:
                    raise ValueError(f"{label}: compiled-Expr step audit did not pass in CI")
                if step_map_info is not None and chk_sa.get("step_map_sha256") != step_map_info["step_map_sha256"]:
                    raise ValueError(f"{label}: CI step_map_sha256 differs from project step_map")
                if prior.get("step_audit") and chk_sa.get("step_map_sha256") != prior["step_audit"].get("step_map_sha256"):
                    raise ValueError(f"{label}: CI step_map_sha256 differs from local receipt")
                supplied_count = step_map_info["supplied_step_count"] if step_map_info is not None else len(chk_sa.get("steps") or [])
                paper_count = step_map_info["paper_step_count"] if step_map_info is not None else 0
                step_meta = dict(
                    step_map_sha256=chk_sa["step_map_sha256"],
                    step_count=chk_sa["step_count"],
                    paper_steps=paper_count,
                    supplied_steps=supplied_count,
                    step_badge=(STEP_VERIFIED_SUPPLIED_BADGE if supplied_count > 0 else STEP_VERIFIED_PAPER_BADGE),
                )

            pkg_proof_modules.extend(targets)
            pkg_claim_records[label] = dict(
                audit_sha256=digest,
                declaration=checked["declaration"],
                expected=checked["expected"],
                axioms=checked["axioms"],
                toolchain=checked["toolchain"],
                theorem_info=bool(checked["theorem_info"]),
                hygiene=hygiene,
                statements=list(checked.get("statements") or []),
                routine=list(checked.get("routine") or []),
                assumes=[],
                statement_sha256=fingerprint,
                hypotheses=(checked.get("hypotheses") or {}).get("proposition"),
                **step_meta,
            )

        pkg_kernels = ["lean-kernel"]
        if ci_level == "paranoid":
            pkg_rel = package.relative_to(root).as_posix()
            harness = generate_challenge_harness(root, package=pkg_rel, write=False)
            pkg_harness = harness["packages"][pkg_rel]
            created_temp = []
            try:
                for fname, expected_bytes in (
                    ("Challenge.lean", pkg_harness["_challenge_bytes"]),
                    ("Solution.lean", pkg_harness["_solution_bytes"]),
                ):
                    fpath = package / fname
                    if fpath.is_file():
                        if fpath.read_bytes() != expected_bytes:
                            raise ValueError(
                                f"{pkg_rel}: committed {fname} differs from hash-locked generated harness"
                            )
                    else:
                        fpath.write_bytes(expected_bytes)
                        created_temp.append(fpath)

                harness_check = verify_challenge_solution_lean(package, pkg_harness, pkg_env, lake)
                pkg_kernels = run_paranoid_checkers(
                    package, pkg_harness, pin, pkg_proof_modules, pkg_env, lake,
                )
            finally:
                for temp_path in created_temp:
                    temp_path.unlink(missing_ok=True)

            challenge_harnesses[pkg_rel] = dict(
                challenge_file=pkg_harness["challenge_file"],
                solution_file=pkg_harness["solution_file"],
                challenge_sha256=harness_check["challenge_sha256"],
                solution_sha256=harness_check["solution_sha256"],
                statements_sha256=harness_check["statements_sha256"],
                targets_checked=harness_check["targets_checked"],
                lakefile_configured=pkg_harness["lakefile_configured"],
                kernels_checked=pkg_kernels,
            )

        all_kernels = _dedup_ordered([*all_kernels, *pkg_kernels])
        for label, rec in pkg_claim_records.items():
            rec["kernels_checked"] = list(pkg_kernels)
            result["claims"][label] = rec

    result["kernels_checked"] = all_kernels
    if challenge_harnesses:
        result["challenge_harness"] = challenge_harnesses
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", nargs="?", type=Path, help="Path to write lean-verification.json")
    parser.add_argument("--prepare-only", action="store_true",
                        help="Materialize locked dependencies and Mathlib caches without running verification")
    parser.add_argument("--install-paranoid-tools", type=Path, metavar="BIN_DIR",
                        help="Install pinned lean4checker into BIN_DIR for toolchains < v4.35.0")
    parser.add_argument("--offline", action="store_true",
                        help="Skip network dependency/cache preparation and run verification strictly offline")
    parser.add_argument("--level", choices=["standard", "paranoid"],
                        help="Override hosting.lean_ci_level from project.json")
    args = parser.parse_args()
    try:
        if args.prepare_only:
            prepare_project(Path.cwd(), level=args.level)
        elif args.install_paranoid_tools:
            install_paranoid_tools(Path.cwd(), args.install_paranoid_tools)
        else:
            if not args.output:
                parser.error("output path is required unless --prepare-only or --install-paranoid-tools is given")
            args.output.write_text(
                json.dumps(verify(Path.cwd(), offline=args.offline, level=args.level), indent=2) + "\n",
                encoding="utf-8",
            )
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as exc:
        sys.exit(str(exc))
