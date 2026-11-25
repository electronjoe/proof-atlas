"""Recheck closed atlas claims on a clean GitHub runner and emit per-claim evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
from types import SimpleNamespace

from atlas import local
from audit_lean import audit, import_headers


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


def verify(root):
    project = json.loads((root / "project.json").read_bytes())
    repository = os.environ["GITHUB_REPOSITORY"]
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    if commit != os.environ["GITHUB_SHA"] or project["hosting"]["repository"].casefold() != ("https://github.com/" + repository).casefold():
        raise ValueError("Checkout differs from the requested GitHub revision or repository")
    if project["hosting"].get("lean_ci") != "enabled":
        raise ValueError("GitHub Lean verification is not enabled for this project")
    result = dict(repository=repository, commit=commit, run_id=int(os.environ["GITHUB_RUN_ID"]),
                  attempt=int(os.environ["GITHUB_RUN_ATTEMPT"]), claims={})
    packages = {}
    for label, work in project.get("work", {}).items():
        if work.get("status") != "closed":
            continue
        closure = work["closure"]
        raw = local(root, closure["audit"]).read_bytes()
        prior = json.loads(raw)
        package = local(root, closure["package"])
        if any(hashlib.sha256(local(package, f).read_bytes()).hexdigest() != h for f, h in prior["checked_inputs"].items()):
            raise ValueError(f"{label}: recorded source hashes differ from the checkout")
        if any(closure[key] != prior[key] for key in ("declaration", "expected")):
            raise ValueError(f"{label}: local certificate names differ from the closure")
        if prior.get("assumes") or work.get("assumes"):
            raise ValueError(f"{label}: closed claim cannot carry unresolved conditional assumptions")
        packages.setdefault(package, []).append((label, prior, hashlib.sha256(raw).hexdigest()))
    for package, group in packages.items():
        prepare(package, [prior for _, prior, _ in group])
        for label, prior, digest in group:
            print(f"Rechecking {label} ({prior['declaration']})", flush=True)
            targets = prior.get("targets")
            if not targets:
                imports = import_headers(["lake"], [prior["contract"]], package, os.environ)
                targets = sorted(m for m in imports if (package / (m.replace(".", "/") + ".lean")).is_file())
            checked = audit(SimpleNamespace(package=package, contract=prior["contract"], target=targets,
                                            expected=prior["expected"], declaration=prior["declaration"],
                                            statements=prior.get("statements", []),
                                            routine=prior.get("routine", []),
                                            assumes=prior.get("assumes", []),
                                            witness=prior.get("hypotheses", {}).get("declaration")))
            fingerprint = checked.get("statement", {}).get("sha256")
            if prior.get("statement") and fingerprint != prior["statement"]["sha256"]:
                raise ValueError(f"{label}: statement fingerprint differs from the local receipt")
            result["claims"][label] = dict(audit_sha256=digest, declaration=checked["declaration"],
                                            expected=checked["expected"], axioms=checked["axioms"],
                                            toolchain=checked["toolchain"],
                                            statement_sha256=fingerprint,
                                            hypotheses=checked.get("hypotheses", {}).get("proposition"))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(json.dumps(verify(Path.cwd()), indent=2) + "\n", encoding="utf-8")
