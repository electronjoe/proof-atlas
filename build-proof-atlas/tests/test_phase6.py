"""Phase 6 unit and Lean 4.33.1 integration tests: batched package verification (`audit_batch`)."""
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import atlas
import audit_lean
import verify_ci


def _git(root, *args):
    return subprocess.check_output(["git", *args], cwd=root, text=True).strip()


def _init_git_commit(root, msg="commit"):
    if not (root / ".git").exists():
        _git(root, "init", "-q", "-b", "main")
    _git(root, "add", "-A")
    _git(root, "-c", "user.name=Test", "-c", "user.email=test@example.org", "commit", "-qm", msg)
    return _git(root, "rev-parse", "HEAD")


def _write_source(root, rel, data):
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = data.encode("utf-8") if isinstance(data, str) else data
    path.write_bytes(raw)
    return {"path": rel, "sha256": hashlib.sha256(raw).hexdigest()}


class Phase6UnitTests(unittest.TestCase):
    def test_audit_batch_empty_and_upfront_validation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            other = (root / "other_pkg")
            other.mkdir()
            _write_source(root, "ContractA.lean", "import Statements.Main\n")
            _write_source(root, "lean-toolchain", "leanprover/lean4:v4.33.1\n")
            _write_source(root, "lake-manifest.json", '{"packagesDir": ".lake/packages", "packages": []}\n')

            # Empty batch returns [] without touching Lake.
            with patch.object(audit_lean, "select_lake", side_effect=AssertionError("should not invoke lake")):
                self.assertEqual(audit_lean.audit_batch(root, []), [])

            # Mixed-package specs fail up front before invoking Lake.
            with patch.object(audit_lean, "select_lake", side_effect=AssertionError("should not invoke lake")):
                with self.assertRaisesRegex(ValueError, "same Lean package"):
                    audit_lean.audit_batch(root, [
                        {"package": root, "contract": "ContractA.lean", "expected": "A", "declaration": "mainA"},
                        {"package": other, "contract": "ContractA.lean", "expected": "B", "declaration": "mainB"},
                    ])

            # Invalid identifier in a later claim fails up front before invoking Lake.
            with patch.object(audit_lean, "select_lake", side_effect=AssertionError("should not invoke lake")):
                with self.assertRaisesRegex(ValueError, "fully qualified Lean identifier"):
                    audit_lean.audit_batch(root, [
                        SimpleNamespace(contract="ContractA.lean", expected="A", declaration="mainA"),
                        SimpleNamespace(contract="ContractA.lean", expected="bad name!", declaration="mainB"),
                    ])

    def test_audit_batch_single_build_union_targets_and_pre_post_closures(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            _write_source(root, "lean-toolchain", "leanprover/lean4:v4.33.1\n")
            _write_source(root, "lakefile.toml", (
                'name = "BatchDemo"\n'
                '[[lean_lib]]\nname = "Statements"\n'
                '[[lean_lib]]\nname = "Proofs"\n'
                '[[lean_lib]]\nname = "Examples"\n'
            ))
            _write_source(root, "lake-manifest.json", '{"packagesDir": ".lake/packages", "packages": []}\n')
            _write_source(root, "Statements/Main.lean", "def A : Prop := True\ndef B : Prop := True\n")
            _write_source(root, "Proofs/A.lean", "import Statements.Main\ntheorem mainA : A := trivial\n")
            _write_source(root, "Proofs/B.lean", "import Statements.Main\ntheorem mainB : B := trivial\n")
            _write_source(root, "Examples/Main.lean", "import Statements.Main\ntheorem witB : True := trivial\n")
            _write_source(root, "ContractA.lean", "import Statements.Main\nimport Proofs.A\n")
            _write_source(root, "ContractB.lean", "import Statements.Main\nimport Proofs.B\nimport Examples.Main\n")

            common_meta = {"lean-toolchain", "lakefile.toml", "lake-manifest.json", "Statements/Main.lean"}
            mod_calls = []

            def fake_module_inputs(lake, pkg_root, env, targets, contract_path):
                mod_calls.append((tuple(targets), contract_path))
                if contract_path == "ContractA.lean":
                    return (
                        common_meta | {"ContractA.lean", "Proofs/A.lean"},
                        ["+Proofs.A", "+Statements.Main"],
                    )
                return (
                    common_meta | {"ContractB.lean", "Proofs/B.lean", "Examples/Main.lean"},
                    ["+Examples.Main", "+Proofs.B", "+Statements.Main"],
                )

            build_calls = []

            def fake_run(cmd, cwd, env, log):
                build_calls.append(list(cmd))

            def fake_sub_run(cmd, *, input=b"", **kwargs):
                text = input.decode("utf-8")
                if "mainA" in text:
                    out = "'mainA' does not depend on any axioms\nPROOF-ATLAS-DECL-KIND theorem\n"
                else:
                    out = "'mainB' does not depend on any axioms\nPROOF-ATLAS-DECL-KIND theorem\n"
                return subprocess.CompletedProcess(cmd, 0, out.encode("utf-8"), b"")

            def fake_stmt_record(lake, pkg_root, env, contract_path, expected, *, local_modules=None):
                sha = hashlib.sha256(expected.encode()).hexdigest()
                return (
                    {"expected": expected, "sha256": sha,
                     "constants": [{"name": expected, "file": "Statements/Main.lean", "lines": [1, 1], "sha256": sha}]},
                    [],
                )

            def fake_proof_closure(lake, pkg_root, env, contract_path, declaration, expected,
                                   statement_modules=(), *, local_modules=None):
                mod = "Proofs.A" if declaration == "mainA" else "Proofs.B"
                return {
                    "used_local_theorems": [],
                    "used_local_statements": [],
                    "reachable_local_defs": 1,
                    "reachable_local_theorems": 0,
                    "_reachable_modules": ["Statements.Main", mod],
                }

            def fake_hyp(lake, pkg_root, env, contract_path, expected, witness, *, local_modules=None):
                return {"declaration": witness, "proposition": "True", "axioms": []}

            specs = [
                SimpleNamespace(
                    package=root, contract="ContractA.lean", expected="A", declaration="mainA",
                    target=["Proofs.A"], statements=["Statements"],
                ),
                SimpleNamespace(
                    package=root, contract="ContractB.lean", expected="B", declaration="mainB",
                    target=["Proofs.B"], statements=["Statements"], witness="witB",
                ),
            ]

            with patch.object(audit_lean, "select_lake", return_value=["lake"]), \
                 patch.object(audit_lean, "module_inputs", side_effect=fake_module_inputs), \
                 patch.object(audit_lean, "check_routine", return_value=[]), \
                 patch.object(audit_lean, "run", side_effect=fake_run), \
                 patch.object(audit_lean.subprocess, "run", side_effect=fake_sub_run), \
                 patch.object(audit_lean, "check_statements", return_value=["Statements.Main"]), \
                 patch.object(audit_lean, "statement_record", side_effect=fake_stmt_record), \
                 patch.object(audit_lean, "proof_closure_record", side_effect=fake_proof_closure), \
                 patch.object(audit_lean, "hypotheses_record", side_effect=fake_hyp), \
                 patch.object(sys, "stderr", io.StringIO()):
                receipts = audit_lean.audit_batch(root, specs)

            # Exactly ONE batched build with the deduplicated union of explicit + contract targets.
            self.assertEqual(len(build_calls), 1)
            self.assertEqual(
                build_calls[0],
                ["lake", "--no-cache", "build", "Proofs.A", "Proofs.B", "+Statements.Main", "+Examples.Main"],
            )
            # module_inputs ran pre-build (2 calls) AND re-ran fresh post-check (2 calls).
            self.assertEqual(len(mod_calls), 4)
            self.assertEqual(len(receipts), 2)
            # Per-claim checked_inputs remain isolated to each claim's own closure.
            self.assertIn("Proofs/A.lean", receipts[0]["checked_inputs"])
            self.assertNotIn("Proofs/B.lean", receipts[0]["checked_inputs"])
            self.assertIn("Proofs/B.lean", receipts[1]["checked_inputs"])
            self.assertIn("Examples/Main.lean", receipts[1]["checked_inputs"])
            self.assertNotIn("Proofs/A.lean", receipts[1]["checked_inputs"])

            # Pre-build hygiene violation in Claim 2 fails BEFORE calling `lake --no-cache build`.
            _write_source(root, "Proofs/B.lean", "import Statements.Main\n#eval 1 + 1\ntheorem mainB : B := trivial\n")
            with patch.object(audit_lean, "select_lake", return_value=["lake"]), \
                 patch.object(audit_lean, "module_inputs", side_effect=fake_module_inputs), \
                 patch.object(audit_lean, "check_routine", return_value=[]), \
                 patch.object(audit_lean, "run", side_effect=AssertionError("build should not run on hygiene failure")):
                with self.assertRaisesRegex(ValueError, r"Proofs/B\.lean:2: #eval"):
                    audit_lean.audit_batch(root, specs)

            # Restore Proofs/B.lean and confirm post-check detects mid-build mutation in Claim 2's closure.
            _write_source(root, "Proofs/B.lean", "import Statements.Main\ntheorem mainB : B := trivial\n")

            def mutate_claim2_during_build(cmd, cwd, env, log):
                (root / "Proofs/B.lean").write_text(
                    "import Statements.Main\n-- mutated mid-build\ntheorem mainB : B := trivial\n",
                    encoding="utf-8",
                )

            with patch.object(audit_lean, "select_lake", return_value=["lake"]), \
                 patch.object(audit_lean, "module_inputs", side_effect=fake_module_inputs), \
                 patch.object(audit_lean, "check_routine", return_value=[]), \
                 patch.object(audit_lean, "run", side_effect=mutate_claim2_during_build), \
                 patch.object(audit_lean.subprocess, "run", side_effect=fake_sub_run), \
                 patch.object(audit_lean, "check_statements", return_value=["Statements.Main"]), \
                 patch.object(audit_lean, "statement_record", side_effect=fake_stmt_record), \
                 patch.object(audit_lean, "proof_closure_record", side_effect=fake_proof_closure), \
                 patch.object(audit_lean, "hypotheses_record", side_effect=fake_hyp), \
                 patch.object(sys, "stderr", io.StringIO()):
                with self.assertRaisesRegex(ValueError, "Package inputs changed during the audit"):
                    audit_lean.audit_batch(root, specs)

    def test_verify_ci_batches_per_package_across_multiple_packages(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            tex = _write_source(root, "paper.tex", (
                r"\begin{lemma}\label{lem:a}A.\end{lemma}" "\n"
                r"\begin{theorem}\label{thm:b}B.\end{theorem}" "\n"
                r"\begin{corollary}\label{cor:c}C.\end{corollary}" "\n"
            ))
            pdf = _write_source(root, "paper.pdf", b"%PDF-1.4")

            def make_pkg(pkg_name, claim_specs):
                tc = _write_source(root, f"{pkg_name}/lean-toolchain", "leanprover/lean4:v4.33.1\n")
                lf = _write_source(root, f"{pkg_name}/lakefile.toml", (
                    f'name = "{pkg_name}"\n[[lean_lib]]\nname = "Statements"\n[[lean_lib]]\nname = "Proofs"\n'
                ))
                lm = _write_source(root, f"{pkg_name}/lake-manifest.json", '{"packagesDir": ".lake/packages", "packages": []}\n')
                st = _write_source(root, f"{pkg_name}/Statements/Main.lean", "def P : Prop := True\n")
                priors = {}
                work = {}
                for cid, decl, mod in claim_specs:
                    pf_rel = mod.replace(".", "/") + ".lean"
                    pf = _write_source(root, f"{pkg_name}/{pf_rel}", f"import Statements.Main\ntheorem {decl} : P := trivial\n")
                    ct = _write_source(root, f"{pkg_name}/Contract_{decl}.lean", f"import Statements.Main\nimport {mod}\n")
                    checked_inputs = {
                        "Statements/Main.lean": st["sha256"],
                        pf_rel: pf["sha256"],
                        f"Contract_{decl}.lean": ct["sha256"],
                        "lean-toolchain": tc["sha256"],
                        "lakefile.toml": lf["sha256"],
                        "lake-manifest.json": lm["sha256"],
                    }
                    sha = hashlib.sha256(f"{pkg_name}:{decl}".encode()).hexdigest()
                    prior = {
                        "declaration": decl, "contract": f"Contract_{decl}.lean", "expected": "P",
                        "toolchain": "leanprover/lean4:v4.33.1", "axioms": [],
                        "theorem_info": True, "targets": [mod], "input_scope": "module-closure",
                        "checked_inputs": checked_inputs, "statements": ["Statements"],
                        "hygiene": {"checked": True, "statements_checked": True},
                        "statement": {"expected": "P", "sha256": sha,
                                      "constants": [{"name": "P", "file": "Statements/Main.lean", "lines": [1, 1], "sha256": sha}]},
                    }
                    ev_rel = f"evidence/{decl}.json"
                    _write_source(root, ev_rel, json.dumps(prior))
                    priors[(pkg_name, decl)] = prior
                    work[cid] = {
                        "status": "closed", "scope": cid, "run_log": f"{decl}.log",
                        "checked_inputs": {f"{pkg_name}/{k}": v for k, v in checked_inputs.items()},
                        "closure": {"package": pkg_name, "expected": "P", "declaration": decl,
                                    "audit": ev_rel, "correspondence": cid},
                    }
                return priors, work

            priors1, work1 = make_pkg("pkg_one", [("lem:a", "mainA", "Proofs.A"), ("thm:b", "mainB", "Proofs.B")])
            priors2, work2 = make_pkg("pkg_two", [("cor:c", "mainC", "Proofs.C")])
            all_priors = {**priors1, **priors2}
            project = {
                "schema_version": 1, "environments": ["lemma", "theorem", "corollary"],
                "edition": "test", "title": "Multi-Package Batch CI", "tex": [tex], "pdf": pdf,
                "hosting": {"decision": "github", "repository": "https://github.com/example/batch-ci",
                            "lean_ci": "enabled", "lean_ci_level": "standard"},
                "work": {**work1, **work2},
            }
            (root / "project.json").write_text(json.dumps(project), encoding="utf-8")
            head = _init_git_commit(root)

            env_patch = {
                "GITHUB_REPOSITORY": "example/batch-ci",
                "GITHUB_SHA": head,
                "GITHUB_RUN_ID": "601",
                "GITHUB_RUN_ATTEMPT": "1",
            }
            batch_invocations = []

            def fake_audit_batch(package, specs, *, lake=None, env=None):
                pkg_name = package.relative_to(root).as_posix()
                batch_invocations.append((pkg_name, [s.declaration for s in specs]))
                return [dict(all_priors[(pkg_name, s.declaration)]) for s in specs]

            with patch.dict(os.environ, env_patch, clear=False), \
                 patch.object(verify_ci, "select_lake", return_value=["lake"]), \
                 patch.object(verify_ci, "audit_batch", side_effect=fake_audit_batch), \
                 redirect_stdout(io.StringIO()):
                res = verify_ci.verify(root, offline=True)

            # One audit_batch call per package (2 packages, 3 total claims).
            self.assertEqual(len(batch_invocations), 2)
            by_pkg = dict(batch_invocations)
            self.assertEqual(by_pkg["pkg_one"], ["mainA", "mainB"])
            self.assertEqual(by_pkg["pkg_two"], ["mainC"])
            self.assertEqual(set(res["claims"]), {"lem:a", "thm:b", "cor:c"})
            self.assertEqual(res["kernels_checked"], ["lean-kernel"])
            self.assertEqual(res["checks_enforced"], list(verify_ci.PARITY_CHECKS))


@unittest.skipUnless(os.environ.get("ELAN_TOOLCHAIN"), "requires an installed pinned Lean toolchain")
class Phase6LeanIntegration(unittest.TestCase):
    def test_live_lean_audit_batch_receipt_parity_and_single_build(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            pin = os.environ["ELAN_TOOLCHAIN"]
            (root / "lean-toolchain").write_text(pin + "\n", encoding="utf-8")
            (root / "lakefile.toml").write_text(
                'name = "Phase6Parity"\n'
                '[[lean_lib]]\nname = "Prelude"\n'
                '[[lean_lib]]\nname = "Statements"\n'
                '[[lean_lib]]\nname = "Routine"\n'
                '[[lean_lib]]\nname = "Proofs"\n'
                '[[lean_lib]]\nname = "Examples"\n',
                encoding="utf-8",
            )
            sources = {
                "Prelude.lean": "-- pure external imports only\n",
                "Statements/Main.lean": (
                    "import Prelude\n"
                    "def gap (a b : Nat) : Nat := a - b\n"
                    "noncomputable def picked (h : ∃ n : Nat, 0 < n) : Nat := Classical.choose h\n"
                    "def LemA : Prop := ∀ n : Nat, n = n\n"
                    "def ThmB : Prop := ∀ n : Nat, 0 < n → gap n 1 < n\n"
                    "def CorC : Prop := ∀ (h : ∃ n : Nat, 0 < n), picked h + 1 > picked h\n"
                ),
                "Routine/Glue.lean": (
                    "import Prelude\n"
                    "theorem sub_one_lt (n : Nat) (h : 0 < n) : n - 1 < n := by omega\n"
                ),
                "Proofs/A.lean": (
                    "import Statements.Main\n"
                    "namespace ProofsA\n"
                    "theorem main : LemA := fun _ => rfl\n"
                    "end ProofsA\n"
                ),
                "Proofs/B.lean": (
                    "import Statements.Main\nimport Routine.Glue\n"
                    "namespace ProofsB\n"
                    "theorem main (_hA : LemA) : ThmB := fun n h => by unfold gap; exact sub_one_lt n h\n"
                    "end ProofsB\n"
                ),
                "Proofs/C.lean": (
                    "import Statements.Main\n"
                    "namespace ProofsC\n"
                    "theorem main : CorC := fun h => Nat.lt_succ_self (picked h)\n"
                    "end ProofsC\n"
                ),
                "Examples/Main.lean": (
                    "import Statements.Main\n"
                    "theorem witB : ∃ n : Nat, 0 < n := ⟨1, by decide⟩\n"
                ),
                "ContractA.lean": "import Statements.Main\nimport Proofs.A\n",
                "ContractB.lean": "import Statements.Main\nimport Proofs.B\nimport Examples.Main\n",
                "ContractC.lean": "import Statements.Main\nimport Proofs.C\n",
                "StmtContractB.lean": "import Statements.Main\nimport Examples.Main\n",
            }
            for rel, body in sources.items():
                _write_source(root, rel, body)

            env = os.environ.copy()
            lake = audit_lean.select_lake(root, pin, env, sys.stderr, offline=True)
            subprocess.run([*lake, "update"], cwd=root, env=env, check=True)

            specs = [
                SimpleNamespace(
                    package=root, contract="ContractA.lean", expected="LemA", declaration="ProofsA.main",
                    target=["Proofs.A"], statements=["Statements"],
                ),
                SimpleNamespace(
                    package=root, contract="ContractB.lean", expected="ThmB", declaration="ProofsB.main",
                    target=["Proofs.B"], statements=["Statements"], routine=["Routine"],
                    assumes=["LemA"], witness="witB",
                ),
                SimpleNamespace(
                    package=root, contract="ContractC.lean", expected="CorC", declaration="ProofsC.main",
                    target=["Proofs.C"], statements=["Statements"],
                ),
                SimpleNamespace(
                    package=root, contract="StmtContractB.lean", expected="ThmB",
                    statements=["Statements"], witness="witB", statement_only=True,
                ),
            ]

            # 1. Sequential baseline via `audit()`.
            seq_receipts = [audit_lean.audit(spec) for spec in specs]

            # 2. Batched execution via `audit_batch()` while recording `lake --no-cache build` invocations.
            build_cmds = []
            real_run = audit_lean.run

            def spy_run(cmd, cwd, run_env, log):
                build_cmds.append(list(cmd))
                return real_run(cmd, cwd, run_env, log)

            with patch.object(audit_lean, "run", side_effect=spy_run):
                batch_receipts = audit_lean.audit_batch(root, specs)

            # Exactly ONE `lake --no-cache build <union-of-targets>` invocation for all 4 specs.
            self.assertEqual(len(build_cmds), 1)
            build_args = build_cmds[0]
            self.assertIn("--no-cache", build_args)
            self.assertIn("build", build_args)
            targets_passed = build_args[build_args.index("build") + 1:]
            self.assertEqual(
                targets_passed,
                ["Proofs.A", "Proofs.B", "Proofs.C", "+Statements.Main", "+Examples.Main"],
            )

            # 100% receipt parity between sequential `audit()` and batched `audit_batch()`.
            self.assertEqual(len(batch_receipts), len(seq_receipts))
            for idx, (seq_r, bat_r) in enumerate(zip(seq_receipts, batch_receipts)):
                self.assertEqual(bat_r, seq_r, f"Receipt mismatch for claim index {idx}")

            # 3. Pre-build hygiene violation in claim #3 blocks the batched build completely.
            orig_c = (root / "Proofs/C.lean").read_text(encoding="utf-8")
            (root / "Proofs/C.lean").write_text(orig_c + '#eval IO.println "bad"\n', encoding="utf-8")
            with patch.object(audit_lean, "run", side_effect=AssertionError("build should not run")):
                with self.assertRaisesRegex(ValueError, r"Proofs/C\.lean:5: #eval"):
                    audit_lean.audit_batch(root, specs)
            (root / "Proofs/C.lean").write_text(orig_c, encoding="utf-8")

            # 4. Post-check closure/hash verification catches a mid-build edit to one claim's inputs.
            orig_b = (root / "Proofs/B.lean").read_text(encoding="utf-8")

            def edit_b_after_build(cmd, cwd, run_env, log):
                real_run(cmd, cwd, run_env, log)
                (root / "Proofs/B.lean").write_text(orig_b + "-- changed after build\n", encoding="utf-8")

            with patch.object(audit_lean, "run", side_effect=edit_b_after_build):
                with self.assertRaisesRegex(ValueError, "Package inputs changed during the audit"):
                    audit_lean.audit_batch(root, specs)
            (root / "Proofs/B.lean").write_text(orig_b, encoding="utf-8")

    def test_live_lean_verify_ci_batched_standard_and_paranoid(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            pin = os.environ["ELAN_TOOLCHAIN"]
            tex = _write_source(root, "paper.tex", (
                r"\begin{lemma}\label{lem:a}Reflexivity lemma.\end{lemma}" "\n"
                r"\begin{theorem}\label{thm:b}Add-zero theorem.\end{theorem}" "\n"
                r"\begin{corollary}\label{cor:c}Double-zero corollary.\end{corollary}" "\n"
            ))
            pdf = _write_source(root, "paper.pdf", b"%PDF-1.4")
            pkg = root / "lean"
            pkg.mkdir()
            (pkg / "lean-toolchain").write_text(pin + "\n", encoding="utf-8")
            (pkg / "lakefile.toml").write_text(
                'name = "Phase6CIDemo"\n'
                '[[lean_lib]]\nname = "Prelude"\n'
                '[[lean_lib]]\nname = "Statements"\n'
                '[[lean_lib]]\nname = "Routine"\n'
                '[[lean_lib]]\nname = "Proofs"\n'
                '[[lean_lib]]\nname = "Examples"\n'
                '[[lean_lib]]\nname = "Assembly"\n'
                '[[lean_lib]]\nname = "Challenge"\n'
                '[[lean_lib]]\nname = "Solution"\n',
                encoding="utf-8",
            )
            sources = {
                "Prelude.lean": "-- pure external imports only\n",
                "Statements/Main.lean": (
                    "import Prelude\n"
                    "def LemA : Prop := ∀ n : Nat, n = n\n"
                    "def ThmB : Prop := ∀ n : Nat, 0 < n → n + 0 = n\n"
                    "def CorC : Prop := ∀ n : Nat, 0 < n → (n + 0) + 0 = n\n"
                ),
                "Routine/Glue.lean": (
                    "import Prelude\n"
                    "theorem add_zero_glue (n : Nat) : n + 0 = n := Nat.add_zero n\n"
                ),
                "Proofs/A.lean": (
                    "import Statements.Main\nnamespace ProofsA\n"
                    "theorem main : LemA := fun _ => rfl\nend ProofsA\n"
                ),
                "Proofs/B.lean": (
                    "import Statements.Main\nimport Routine.Glue\nnamespace ProofsB\n"
                    "theorem main (_hA : LemA) : ThmB := fun n _ => add_zero_glue n\nend ProofsB\n"
                ),
                "Proofs/C.lean": (
                    "import Statements.Main\nnamespace ProofsC\n"
                    "theorem main (hB : ThmB) : CorC := fun n h => (congrArg (· + 0) (hB n h)).trans (hB n h)\nend ProofsC\n"
                ),
                "Examples/Main.lean": (
                    "import Statements.Main\n"
                    "theorem witB : ∃ n : Nat, 0 < n := ⟨1, by decide⟩\n"
                ),
                "ContractA.lean": "import Statements.Main\nimport Proofs.A\n",
            }
            for rel, body in sources.items():
                _write_source(pkg, rel, body)

            env = os.environ.copy()
            lake = audit_lean.select_lake(pkg, pin, env, sys.stderr, offline=True)
            subprocess.run([*lake, "update"], cwd=pkg, env=env, check=True)

            # Audit lem:a directly via Proofs.A and assemble thm:b + cor:c via Assembly.lean,
            # exercising mixed contracts and targets inside a single package batch in verify_ci.
            project = {
                "schema_version": 1, "environments": ["lemma", "theorem", "corollary"],
                "edition": "test-v1", "title": "Phase 6 Live CI Batch Test",
                "tex": [tex], "pdf": pdf,
                "proof_work": {"mode": "paper"},
                "hosting": {
                    "decision": "github",
                    "repository": "https://github.com/example/phase6-ci",
                    "site": "https://example.github.io/phase6-ci/",
                    "visibility": "public",
                    "lean_ci": "enabled",
                    "lean_ci_level": "standard",
                },
                "work": {
                    "lem:a": {
                        "status": "drafted", "scope": "Lemma A.", "updated": "2026-11-26T00:00:00Z",
                        "assembly": {
                            "package": "lean", "module": "Proofs.A", "declaration": "ProofsA.main",
                            "expected": "LemA", "assumes": [],
                            "statements": ["Statements"], "statement_modules": ["Statements.Main"],
                        },
                    },
                    "thm:b": {
                        "status": "drafted", "scope": "Theorem B.", "updated": "2026-11-26T00:00:00Z",
                        "assembly": {
                            "package": "lean", "module": "Proofs.B", "declaration": "ProofsB.main",
                            "expected": "ThmB", "assumes": ["lem:a"],
                            "statements": ["Statements"], "routine": ["Routine"],
                            "witness": "witB", "witness_modules": ["Examples.Main"],
                            "statement_modules": ["Statements.Main"],
                        },
                    },
                    "cor:c": {
                        "status": "drafted", "scope": "Corollary C.", "updated": "2026-11-26T00:00:00Z",
                        "assembly": {
                            "package": "lean", "module": "Proofs.C", "declaration": "ProofsC.main",
                            "expected": "CorC", "assumes": ["thm:b"],
                            "statements": ["Statements"], "witness": "witB",
                            "witness_modules": ["Examples.Main"], "statement_modules": ["Statements.Main"],
                        },
                    },
                },
            }
            (root / "project.json").write_text(json.dumps(project, indent=2), encoding="utf-8")
            with redirect_stdout(io.StringIO()):
                atlas.assemble(root, run_audit=True)

            # Also point lem:a directly to its standalone ContractA.lean + Proofs.A receipt so
            # verify_ci batches heterogeneous contracts/targets (Proofs.A + Assembly) in one build.
            ev_a = audit_lean.audit(SimpleNamespace(
                package=pkg, contract="ContractA.lean", expected="LemA", declaration="ProofsA.main",
                target=["Proofs.A"], statements=["Statements"],
            ))
            _write_source(root, "evidence/lem-a.json", json.dumps(ev_a, indent=2) + "\n")
            proj_data = json.loads((root / "project.json").read_text(encoding="utf-8"))
            proj_data["work"]["lem:a"]["closure"] = {
                "package": "lean", "expected": "LemA", "declaration": "ProofsA.main",
                "audit": "evidence/lem-a.json", "correspondence": "Lemma A.",
            }
            proj_data["work"]["lem:a"]["checked_inputs"] = {
                f"lean/{k}": v for k, v in ev_a["checked_inputs"].items()
            }
            (root / "project.json").write_text(json.dumps(proj_data, indent=2), encoding="utf-8")

            atlas.generate_challenge_harness(root)
            (root / "comparisons.json").write_text("{}\n", encoding="utf-8")
            head = _init_git_commit(root, "phase 6 live ci")

            ci_env = {
                "GITHUB_REPOSITORY": "example/phase6-ci",
                "GITHUB_SHA": head,
                "GITHUB_RUN_ID": "602",
                "GITHUB_RUN_ATTEMPT": "1",
            }

            # 1. Standard CI: verify exactly ONE batched `lake --no-cache build` across all 3 claims.
            std_builds = []
            real_run = audit_lean.run

            def spy_std_run(cmd, cwd, run_env, log):
                std_builds.append(list(cmd))
                return real_run(cmd, cwd, run_env, log)

            with patch.dict(os.environ, ci_env, clear=False), \
                 patch.object(audit_lean, "run", side_effect=spy_std_run), \
                 redirect_stdout(io.StringIO()):
                std_res = verify_ci.verify(root, offline=True, level="standard")

            self.assertEqual(len(std_builds), 1)
            self.assertIn("Proofs.A", std_builds[0])
            self.assertIn("Assembly", std_builds[0])
            self.assertEqual(set(std_res["claims"]), {"lem:a", "thm:b", "cor:c"})
            self.assertEqual(std_res["ci_level"], "standard")
            self.assertEqual(std_res["kernels_checked"], ["lean-kernel"])
            self.assertEqual(std_res["checks_enforced"], list(verify_ci.PARITY_CHECKS))
            self.assertEqual(std_res["claims"]["thm:b"]["routine"], ["Routine.Glue"])
            self.assertEqual(std_res["claims"]["thm:b"]["hypotheses"], "∃ n, 0 < n")
            self.assertEqual(std_res["claims"]["cor:c"]["hypotheses"], "∃ n, 0 < n")
            self.assertTrue(all(rec["theorem_info"] for rec in std_res["claims"].values()))

            # 2. Paranoid CI: single batched `audit_batch` build + full Challenge/Solution + checkers.
            stub_dir = Path(tempfile.mkdtemp(dir=tmp))
            comp_bin = stub_dir / "fake_comparator.py"
            comp_bin.write_text(
                f"#!{sys.executable}\n"
                "import json, pathlib, sys\n"
                "cfg = json.loads(pathlib.Path(sys.argv[1]).read_text())\n"
                "assert len(cfg['theorem_names']) == 3\n",
                encoding="utf-8",
            )
            comp_bin.chmod(comp_bin.stat().st_mode | stat.S_IXUSR)

            l4c_bin = stub_dir / "fake_lean4checker.py"
            l4c_bin.write_text(
                f"#!{sys.executable}\n"
                "import sys\n"
                "assert sys.argv[1] == '--fresh' and 'Solution' in sys.argv[2:]\n",
                encoding="utf-8",
            )
            l4c_bin.chmod(l4c_bin.stat().st_mode | stat.S_IXUSR)

            p_builds = []

            def spy_p_run(cmd, cwd, run_env, log):
                p_builds.append(list(cmd))
                return real_run(cmd, cwd, run_env, log)

            p_env = dict(
                ci_env,
                COMPARATOR_BIN=str(comp_bin),
                LEAN4CHECKER_BIN=str(l4c_bin),
                PROOF_ATLAS_NETWORK_ISOLATED="1",
            )
            with patch.dict(os.environ, p_env, clear=False), \
                 patch.object(audit_lean, "run", side_effect=spy_p_run), \
                 redirect_stdout(io.StringIO()):
                p_res = verify_ci.verify(root, offline=True, level="paranoid")

            self.assertEqual(len(p_builds), 1)
            self.assertEqual(p_res["ci_level"], "paranoid")
            self.assertTrue(p_res["network_isolated"])
            self.assertEqual(p_res["kernels_checked"], ["lean-kernel", "comparator", "lean4checker"])
            self.assertEqual(len(p_res["challenge_harness"]["lean"]["targets_checked"]), 3)
            for cid in ("lem:a", "thm:b", "cor:c"):
                self.assertEqual(p_res["claims"][cid]["kernels_checked"], ["lean-kernel", "comparator", "lean4checker"])


if __name__ == "__main__":
    unittest.main()
