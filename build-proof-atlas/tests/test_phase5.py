"""Phase 5 unit and Lean 4.33.1 integration tests: CI parity, Challenge/Solution harness, and paranoid CI."""
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
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import atlas
import audit_lean
import hosting
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


class Phase5UnitTests(unittest.TestCase):
    def test_lean_version_parsing_and_lake_paranoid_support(self):
        self.assertEqual(verify_ci.parse_lean_version("leanprover/lean4:v4.33.1"), (4, 33, 1))
        self.assertFalse(verify_ci.supports_lake_paranoid("leanprover/lean4:v4.33.1"))
        self.assertEqual(verify_ci.parse_lean_version("leanprover/lean4:v4.35.0"), (4, 35, 0))
        self.assertTrue(verify_ci.supports_lake_paranoid("leanprover/lean4:v4.35.0"))
        self.assertEqual(verify_ci.parse_lean_version("leanprover/lean4:v4.35.0-rc1"), (4, 35, 0))
        self.assertTrue(verify_ci.supports_lake_paranoid("leanprover/lean4:v4.35.0-rc1"))
        self.assertEqual(verify_ci.parse_lean_version("leanprover/lean4:4.36.2"), (4, 36, 2))
        self.assertTrue(verify_ci.supports_lake_paranoid("leanprover/lean4:4.36.2"))
        self.assertIsNone(verify_ci.parse_lean_version("custom-nightly"))
        self.assertFalse(verify_ci.supports_lake_paranoid("custom-nightly"))

    def test_hosting_lean_ci_level_cli_and_workflow_template(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            (root / "project.json").write_text(json.dumps({"schema_version": 1}), encoding="utf-8")

            def run_hosting(*args):
                with patch.object(sys, "argv", ["hosting.py", str(root), *args]), redirect_stdout(io.StringIO()) as out:
                    hosting.main()
                return json.loads((root / "project.json").read_text(encoding="utf-8"))["hosting"], out.getvalue()

            h, _ = run_hosting("--github", "example/paper", "--visibility", "public", "--pages")
            self.assertEqual(h["decision"], "github")

            # Enabling --lean-ci defaults lean_ci_level to "standard" and installs verify-lean.yml.
            h, _ = run_hosting("--lean-ci")
            self.assertEqual(h["lean_ci"], "enabled")
            self.assertEqual(h["lean_ci_level"], "standard")
            wf = (root / ".github/workflows/verify-lean.yml").read_text(encoding="utf-8")
            self.assertIn("lean_ci_level", wf)
            self.assertIn("--prepare-only", wf)
            self.assertIn("--install-paranoid-tools", wf)
            self.assertIn("unshare", wf)
            self.assertIn("--offline", wf)

            # Standalone --lean-ci-level switches an enabled project to paranoid and back.
            h, _ = run_hosting("--lean-ci-level", "paranoid")
            self.assertEqual(h["lean_ci"], "enabled")
            self.assertEqual(h["lean_ci_level"], "paranoid")

            h, _ = run_hosting("--lean-ci-level", "standard")
            self.assertEqual(h["lean_ci_level"], "standard")

            # Combining --lean-ci --lean-ci-level paranoid directly works.
            h, _ = run_hosting("--lean-ci", "--lean-ci-level", "paranoid")
            self.assertEqual(h["lean_ci"], "enabled")
            self.assertEqual(h["lean_ci_level"], "paranoid")

            # Declining removes lean_ci_level once workflow is removed.
            (root / ".github/workflows/verify-lean.yml").unlink()
            h, _ = run_hosting("--no-lean-ci")
            self.assertEqual(h["lean_ci"], "declined")
            self.assertNotIn("lean_ci_level", h)

            # Standalone --lean-ci-level fails when lean_ci is not enabled.
            with self.assertRaises(SystemExit):
                run_hosting("--lean-ci-level", "paranoid")

            # Invalid combination --no-lean-ci --lean-ci-level paranoid fails.
            with self.assertRaises(SystemExit):
                run_hosting("--no-lean-ci", "--lean-ci-level", "paranoid")

    def test_challenge_harness_generation_hash_lock_and_sorry_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            tex = _write_source(root, "paper.tex", (
                r"\begin{lemma}\label{lem:a}Lemma A.\end{lemma}" "\n"
                r"\begin{theorem}\label{thm:b}Theorem B.\end{theorem}" "\n"
            ))
            pdf = _write_source(root, "paper.pdf", b"%PDF-1.4")
            stmt = _write_source(root, "lean/Statements/Main.lean", (
                "def LemA : Prop := ∀ n : Nat, n = n\n"
                "def ThmB : Prop := ∀ n : Nat, n + 0 = n\n"
            ))
            asm = _write_source(root, "lean/Assembly.lean", (
                "import Statements.Main\nnamespace Assembly\n"
                "theorem lem_a : _root_.LemA := fun _ => rfl\nend Assembly\n"
            ))
            pb = _write_source(root, "lean/Proofs/B.lean", (
                "import Statements.Main\ntheorem main : ThmB := Nat.add_zero\n"
            ))
            _write_source(root, "lean/lakefile.toml", (
                'name = "Demo"\n[[lean_lib]]\nname = "Statements"\n'
                '[[lean_lib]]\nname = "Proofs"\n[[lean_lib]]\nname = "Assembly"\n'
                '[[lean_lib]]\nname = "Challenge"\n[[lean_lib]]\nname = "Solution"\n'
            ))

            sha_a = hashlib.sha256(b"LemA").hexdigest()
            sha_b = hashlib.sha256(b"ThmB").hexdigest()
            _write_source(root, "evidence/a.json", json.dumps({
                "declaration": "Assembly.lem_a", "expected": "LemA", "axioms": [],
                "toolchain": "leanprover/lean4:v4.33.1", "targets": ["Assembly"],
                "statements": ["Statements"], "theorem_info": True,
                "checked_inputs": {"Statements/Main.lean": stmt["sha256"], "Assembly.lean": asm["sha256"]},
                "statement": {"expected": "LemA", "sha256": sha_a,
                              "constants": [{"name": "LemA", "file": "Statements/Main.lean", "lines": [1, 1], "sha256": sha_a}]},
            }))
            _write_source(root, "evidence/b.json", json.dumps({
                "declaration": "main", "expected": "ThmB", "axioms": [],
                "toolchain": "leanprover/lean4:v4.33.1", "targets": ["Proofs.B"],
                "statements": ["Statements"], "theorem_info": True,
                "checked_inputs": {"Statements/Main.lean": stmt["sha256"], "Proofs/B.lean": pb["sha256"]},
                "statement": {"expected": "ThmB", "sha256": sha_b,
                              "constants": [{"name": "ThmB", "file": "Statements/Main.lean", "lines": [2, 2], "sha256": sha_b}]},
            }))
            project = {
                "schema_version": 1, "environments": ["lemma", "theorem"],
                "edition": "test", "title": "Harness Demo", "tex": [tex], "pdf": pdf,
                "hosting": {"decision": "local"},
                "work": {
                    "lem:a": {
                        "status": "closed", "scope": "A", "run_log": "a.log",
                        "checked_inputs": {"lean/Statements/Main.lean": stmt["sha256"], "lean/Assembly.lean": asm["sha256"]},
                        "closure": {"package": "lean", "expected": "LemA", "declaration": "Assembly.lem_a",
                                    "audit": "evidence/a.json", "correspondence": "A"},
                    },
                    "thm:b": {
                        "status": "closed", "scope": "B", "run_log": "b.log",
                        "checked_inputs": {"lean/Statements/Main.lean": stmt["sha256"], "lean/Proofs/B.lean": pb["sha256"]},
                        "closure": {"package": "lean", "expected": "ThmB", "declaration": "main",
                                    "audit": "evidence/b.json", "correspondence": "B"},
                    },
                },
            }
            (root / "project.json").write_text(json.dumps(project), encoding="utf-8")

            report = atlas.generate_challenge_harness(root)
            pkg = report["packages"]["lean"]
            self.assertTrue(pkg["lakefile_configured"])
            self.assertEqual(pkg["challenge_imports"], ["Statements.Main"])
            self.assertEqual(pkg["solution_imports"], ["Assembly", "Proofs.B", "Statements.Main"])
            ch_text = (root / "lean/Challenge.lean").read_text(encoding="utf-8")
            sol_text = (root / "lean/Solution.lean").read_text(encoding="utf-8")
            self.assertIn("import Statements.Main", ch_text)
            self.assertNotIn("import Assembly", ch_text)
            self.assertNotIn("import Proofs", ch_text)
            self.assertIn("theorem lem_a : _root_.LemA := by sorry", ch_text)
            self.assertIn("theorem thm_b : _root_.ThmB := by sorry", ch_text)
            self.assertIn("theorem lem_a : _root_.LemA :=\n  _root_.Assembly.lem_a", sol_text)
            self.assertIn("theorem thm_b : _root_.ThmB :=\n  _root_.main", sol_text)
            self.assertIn(pkg["statements_sha256"], ch_text)
            self.assertIn(pkg["statements_sha256"], sol_text)

            # --check mode passes when unmodified and fails if Challenge.lean is tampered with.
            atlas.generate_challenge_harness(root, write=False, check_only=True)
            (root / "lean/Challenge.lean").write_text(ch_text + "-- tamper\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "committed Challenge.lean differs"):
                atlas.generate_challenge_harness(root, write=False, check_only=True)

            # sorry inside Statements/ is rejected immediately.
            (root / "lean/Statements/Main.lean").write_text(
                "def LemA : Prop := ∀ n : Nat, n = n\ntheorem oops : False := sorry\n", encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, r"Disallowed `sorry`.*Statements/Main\.lean:2"):
                atlas.generate_challenge_harness(root)

    def test_verify_ci_parity_rejections_and_paranoid_checkers_mocked(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            tex = _write_source(root, "paper.tex", r"\begin{theorem}\label{t}T.\end{theorem}" "\n")
            pdf = _write_source(root, "paper.pdf", b"%PDF")
            stmt = _write_source(root, "lean/Statements/Main.lean", "def T : Prop := True\n")
            routine = _write_source(root, "lean/Routine/Glue.lean", "theorem g : True := trivial\n")
            proof = _write_source(root, "lean/Proofs/Main.lean", "import Statements.Main\nimport Routine.Glue\ntheorem main : T := g\n")
            contract = _write_source(root, "lean/Contract.lean", "import Statements.Main\nimport Proofs.Main\n")
            tc = _write_source(root, "lean/lean-toolchain", "leanprover/lean4:v4.35.0\n")
            lf = _write_source(root, "lean/lakefile.toml", (
                'name = "Demo"\n[[lean_lib]]\nname = "Statements"\n'
                '[[lean_lib]]\nname = "Routine"\n[[lean_lib]]\nname = "Proofs"\n'
                '[[lean_lib]]\nname = "Challenge"\n[[lean_lib]]\nname = "Solution"\n'
            ))
            lm = _write_source(root, "lean/lake-manifest.json", '{"packagesDir": ".lake/packages", "packages": []}\n')

            stmt_sha = hashlib.sha256(b"T").hexdigest()
            checked_inputs = {
                "Statements/Main.lean": stmt["sha256"],
                "Routine/Glue.lean": routine["sha256"],
                "Proofs/Main.lean": proof["sha256"],
                "Contract.lean": contract["sha256"],
                "lean-toolchain": tc["sha256"],
                "lakefile.toml": lf["sha256"],
                "lake-manifest.json": lm["sha256"],
            }
            prior = {
                "declaration": "main", "contract": "Contract.lean", "expected": "T",
                "toolchain": "leanprover/lean4:v4.35.0", "axioms": [],
                "theorem_info": True, "targets": ["Proofs.Main"],
                "input_scope": "module-closure",
                "checked_inputs": checked_inputs,
                "statements": ["Statements"],
                "routine": ["Routine.Glue"],
                "hygiene": {"checked": True, "statements_checked": True},
                "statement": {"expected": "T", "sha256": stmt_sha,
                              "constants": [{"name": "T", "file": "Statements/Main.lean", "lines": [1, 1], "sha256": stmt_sha}]},
                "hypotheses": {"declaration": "wit", "proposition": "True", "axioms": []},
            }
            _write_source(root, "evidence/t.json", json.dumps(prior))
            project = {
                "schema_version": 1, "environments": ["theorem"],
                "edition": "test", "title": "CI Test", "tex": [tex], "pdf": pdf,
                "hosting": {"decision": "github", "repository": "https://github.com/example/ci",
                            "lean_ci": "enabled", "lean_ci_level": "paranoid"},
                "work": {
                    "t": {
                        "status": "closed", "scope": "T", "run_log": "t.log",
                        "checked_inputs": {f"lean/{k}": v for k, v in checked_inputs.items()},
                        "closure": {"package": "lean", "expected": "T", "declaration": "main",
                                    "audit": "evidence/t.json", "correspondence": "T"},
                    }
                },
            }
            (root / "project.json").write_text(json.dumps(project), encoding="utf-8")
            head = _init_git_commit(root)

            env_patch = {
                "GITHUB_REPOSITORY": "example/ci",
                "GITHUB_SHA": head,
                "GITHUB_RUN_ID": "99",
                "GITHUB_RUN_ATTEMPT": "1",
                "PROOF_ATLAS_NETWORK_ISOLATED": "1",
            }
            audit_calls = []

            def fake_audit_batch(package, specs, *, lake=None, env=None):
                audit_calls.extend(specs)
                return [dict(prior, routine=["Routine.Glue"]) for _ in specs]

            fake_harness_ok = {
                "verified": True, "challenge_sha256": "1" * 64, "solution_sha256": "2" * 64,
                "statements_sha256": "3" * 64, "targets_checked": ["ProofAtlasChallenge.t"],
            }

            with patch.dict(os.environ, env_patch, clear=False), \
                 patch.object(verify_ci, "select_lake", return_value=["lake"]), \
                 patch.object(verify_ci, "audit_batch", side_effect=fake_audit_batch), \
                 patch.object(verify_ci, "verify_challenge_solution_lean", return_value=fake_harness_ok):

                # 1. Paranoid mode fails closed when no independent checker is available.
                with patch.object(verify_ci, "run_comparator", return_value=None), \
                     patch.object(verify_ci, "run_lean4checker", return_value=None), \
                     patch.object(verify_ci, "run_lake_paranoid", return_value=None):
                    with self.assertRaisesRegex(ValueError, "requires at least one independent checker"):
                        verify_ci.verify(root, offline=True)

                # Verify routine module name `Routine.Glue` was normalized to file path + `Routine` dir!
                self.assertIn("Routine/Glue.lean", audit_calls[-1].routine)
                self.assertIn("Routine", audit_calls[-1].routine)
                self.assertEqual(audit_calls[-1].statements, ["Statements"])
                self.assertEqual(audit_calls[-1].witness, "wit")

                # 2. Paranoid mode with Comparator + Lean >= v4.35.0 `lake check --paranoid` (nanoda/lean4lean/con-leche).
                real_sub_run = subprocess.run

                def fake_sub_run(cmd, *a, **kw):
                    if cmd[:3] == ["lake", "check", "--paranoid"]:
                        return subprocess.CompletedProcess(
                            cmd, 0, b"Verified Solution with nanoda, lean4lean, and con-leche kernels.\n", b"",
                        )
                    return real_sub_run(cmd, *a, **kw)

                with patch.object(verify_ci, "run_comparator", return_value=["comparator"]), \
                     patch.object(verify_ci, "run_lean4checker", return_value=None), \
                     patch.object(verify_ci.subprocess, "run", side_effect=fake_sub_run):
                    res = verify_ci.verify(root, offline=True)

                self.assertEqual(res["ci_level"], "paranoid")
                self.assertTrue(res["network_isolated"])
                self.assertEqual(
                    res["kernels_checked"],
                    ["lean-kernel", "comparator", "lake-check-paranoid", "nanoda", "lean4lean", "con-leche"],
                )
                self.assertEqual(res["claims"]["t"]["kernels_checked"], res["kernels_checked"])
                self.assertTrue(res["claims"]["t"]["theorem_info"])
                self.assertEqual(res["claims"]["t"]["assumes"], [])
                self.assertIn("lean", res["challenge_harness"])

                # 3. Parity rejections: non-thmInfo, hygiene failure, witness mismatch, extra CI input.
                with patch.object(verify_ci, "audit_batch", return_value=[dict(prior, theorem_info=False)]):
                    with self.assertRaisesRegex(ValueError, r"kernel theorem \(\.thmInfo\)"):
                        verify_ci.verify(root, offline=True, level="standard")

                with patch.object(verify_ci, "audit_batch", return_value=[dict(prior, hygiene={"checked": True, "statements_checked": False})]):
                    with self.assertRaisesRegex(ValueError, "hygiene check did not cover"):
                        verify_ci.verify(root, offline=True, level="standard")

                bad_hyp = dict(prior, hypotheses={"declaration": "wit", "proposition": "False", "axioms": []})
                with patch.object(verify_ci, "audit_batch", return_value=[bad_hyp]):
                    with self.assertRaisesRegex(ValueError, "witness re-check differs"):
                        verify_ci.verify(root, offline=True, level="standard")

                extra_in = dict(prior, checked_inputs={**checked_inputs, "Proofs/Hidden.lean": "9" * 64})
                with patch.object(verify_ci, "audit_batch", return_value=[extra_in]):
                    with self.assertRaisesRegex(ValueError, "inputs absent from local receipt: Proofs/Hidden.lean"):
                        verify_ci.verify(root, offline=True, level="standard")

            # 4. Pre-audit parity rejections: unchecked subproofs, statement_only receipt, missing assumes on conditional.
            bad_proj = json.loads((root / "project.json").read_text(encoding="utf-8"))
            bad_proj["work"]["t"]["subproofs"] = [{"title": "Part 1", "status": "open"}]
            (root / "project.json").write_text(json.dumps(bad_proj), encoding="utf-8")
            with patch.dict(os.environ, env_patch, clear=False):
                with self.assertRaisesRegex(ValueError, "unchecked subproofs"):
                    verify_ci.verify(root, offline=True, level="standard")

            bad_proj["work"]["t"].pop("subproofs")
            bad_proj["work"]["t"]["status"] = "conditional"
            (root / "project.json").write_text(json.dumps(bad_proj), encoding="utf-8")
            with patch.dict(os.environ, env_patch, clear=False):
                with self.assertRaisesRegex(ValueError, "conditional claim must record non-empty assumes"):
                    verify_ci.verify(root, offline=True, level="standard")

    def test_atlas_build_manifest_and_review_work_paranoid_badges(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            tex = _write_source(root, "paper.tex", r"\begin{theorem}\label{t}Main theorem.\end{theorem}" "\n")
            pdf = _write_source(root, "paper.pdf", b"%PDF")
            stmt = _write_source(root, "lean/Statements/Main.lean", "def T : Prop := True\n")
            proof = _write_source(root, "lean/Proofs/Main.lean", "import Statements.Main\ntheorem main : T := trivial\n")
            _write_source(root, "run.log", "Built Proofs.Main\n")
            stmt_sha = hashlib.sha256(b"T").hexdigest()
            audit = {
                "expected": "T", "declaration": "main", "axioms": [],
                "axiom_profile": "Constructive (0 axioms)", "toolchain": "leanprover/lean4:v4.35.0",
                "statements": ["Statements"], "theorem_info": True,
                "checked_inputs": {"Statements/Main.lean": stmt["sha256"], "Proofs/Main.lean": proof["sha256"]},
                "statement": {"expected": "T", "sha256": stmt_sha,
                              "constants": [{"name": "T", "file": "Statements/Main.lean", "lines": [1, 1], "sha256": stmt_sha}]},
                "hypotheses": {"declaration": "wit", "proposition": "True", "axioms": []},
                "defaults": [],
            }
            audit_info = _write_source(root, "evidence/t.json", json.dumps(audit))
            project = {
                "schema_version": 1, "environments": ["theorem"],
                "edition": "test", "title": "Paranoid Badge Test", "tex": [tex], "pdf": pdf,
                "proof_work": {"mode": "paper"},
                "hosting": {"decision": "github", "repository": "https://github.com/example/paranoid",
                            "site": "https://example.github.io/paranoid/", "visibility": "public",
                            "lean_ci": "enabled", "lean_ci_level": "paranoid"},
                "work": {
                    "t": {
                        "status": "closed", "scope": "Main theorem.", "run_log": "run.log",
                        "checked_inputs": {"lean/Statements/Main.lean": stmt["sha256"], "lean/Proofs/Main.lean": proof["sha256"]},
                        "closure": {"package": "lean", "expected": "T", "declaration": "main",
                                    "audit": "evidence/t.json", "correspondence": "Matches."},
                    }
                },
            }
            (root / "project.json").write_text(json.dumps(project), encoding="utf-8")
            (root / "comparisons.json").write_text("{}\n", encoding="utf-8")
            head = _init_git_commit(root)

            # Standard CI receipt does NOT satisfy lean_ci_level="paranoid" under --require-ci,
            # and displays standard "Machine verified on GitHub" (never falsely claiming paranoid).
            std_ci = {
                "repository": "example/paranoid", "commit": head, "run_id": 10, "attempt": 1,
                "ci_level": "standard", "kernels_checked": ["lean-kernel"],
                "claims": {
                    "t": {"audit_sha256": audit_info["sha256"], "expected": "T", "declaration": "main",
                          "toolchain": "leanprover/lean4:v4.35.0", "axioms": [], "statement_sha256": stmt_sha,
                          "hypotheses": "True", "theorem_info": True, "kernels_checked": ["lean-kernel"]},
                },
            }
            std_path = root / "std-ci.json"
            std_path.write_text(json.dumps(std_ci), encoding="utf-8")
            with redirect_stdout(io.StringIO()):
                atlas.build(root, ci_receipt=std_path, commit=head)
            dash_std = (root / "dist/progress.html").read_text(encoding="utf-8")
            self.assertIn("Machine verified on GitHub", dash_std)
            self.assertNotIn("Multi-kernel / Comparator", dash_std)
            rw_std = atlas.review_work(root, require_ci=True, ci_receipt=std_path)
            self.assertEqual(rw_std["lean_ci_level"], "paranoid")
            self.assertEqual(rw_std["ci_pending"], ["t"])

            # Paranoid CI receipt awards "Multi-kernel / Comparator", displays kernels, and clears ci_pending.
            paranoid_ci = {
                "repository": "example/paranoid", "commit": head, "run_id": 11, "attempt": 1,
                "ci_level": "paranoid",
                "kernels_checked": ["lean-kernel", "comparator", "lean4checker", "nanoda"],
                "claims": {
                    "t": {"audit_sha256": audit_info["sha256"], "expected": "T", "declaration": "main",
                          "toolchain": "leanprover/lean4:v4.35.0", "axioms": [], "statement_sha256": stmt_sha,
                          "hypotheses": "True", "theorem_info": True,
                          "kernels_checked": ["lean-kernel", "comparator", "lean4checker", "nanoda"]},
                },
            }
            p_path = root / "paranoid-ci.json"
            p_path.write_text(json.dumps(paranoid_ci), encoding="utf-8")
            with redirect_stdout(io.StringIO()):
                atlas.build(root, ci_receipt=p_path, commit=head)
            dash_p = (root / "dist/progress.html").read_text(encoding="utf-8")
            self.assertIn("Multi-kernel / Comparator", dash_p)
            self.assertIn("Kernels: lean-kernel, comparator, lean4checker, nanoda", dash_p)
            ver_md = (root / "dist/VERIFICATION.md").read_text(encoding="utf-8")
            self.assertIn("level: `paranoid`", ver_md)
            self.assertIn("`comparator`", ver_md)
            self.assertIn("`nanoda`", ver_md)
            self.assertIn("GitHub Actions paranoid CI", ver_md)
            rw_p = atlas.review_work(root, require_ci=True, ci_receipt=p_path)
            self.assertEqual(rw_p["ci_pending"], [])


@unittest.skipUnless(os.environ.get("ELAN_TOOLCHAIN"), "requires an installed pinned Lean toolchain")
class Phase5LeanIntegration(unittest.TestCase):
    def test_live_lean_verify_ci_parity_challenge_solution_and_paranoid_flow(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            pin = os.environ["ELAN_TOOLCHAIN"]
            tex = _write_source(root, "paper.tex", (
                r"\begin{lemma}\label{lem:a}Reflexivity lemma.\end{lemma}" "\n"
                r"\begin{theorem}\label{thm:b}Add-zero theorem.\end{theorem}" "\n"
            ))
            pdf = _write_source(root, "paper.pdf", b"%PDF-1.4")
            pkg = root / "lean"
            pkg.mkdir()
            (pkg / "lean-toolchain").write_text(pin + "\n", encoding="utf-8")
            (pkg / "lakefile.toml").write_text(
                'name = "Phase5Demo"\n'
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
                ),
                "Routine/Glue.lean": (
                    "import Prelude\n"
                    "theorem add_zero_glue (n : Nat) : n + 0 = n := Nat.add_zero n\n"
                ),
                "Proofs/A.lean": (
                    "import Statements.Main\n"
                    "theorem main : LemA := fun _ => rfl\n"
                ),
                "Proofs/B.lean": (
                    "import Statements.Main\nimport Routine.Glue\n"
                    "theorem main (_hA : LemA) : ThmB := fun n _ => add_zero_glue n\n"
                ),
                "Examples/Main.lean": (
                    "import Statements.Main\n"
                    "theorem witB : ∃ n : Nat, 0 < n := ⟨1, by decide⟩\n"
                ),
            }
            for rel, body in sources.items():
                _write_source(pkg, rel, body)

            env = os.environ.copy()
            lake = audit_lean.select_lake(pkg, pin, env, sys.stderr, offline=True)
            subprocess.run([*lake, "update"], cwd=pkg, env=env, check=True)

            project = {
                "schema_version": 1, "environments": ["lemma", "theorem"],
                "edition": "test-v1", "title": "Phase 5 Live Lean Test",
                "tex": [tex], "pdf": pdf,
                "proof_work": {"mode": "paper"},
                "hosting": {
                    "decision": "github",
                    "repository": "https://github.com/example/phase5-live",
                    "site": "https://example.github.io/phase5-live/",
                    "visibility": "public",
                    "lean_ci": "enabled",
                    "lean_ci_level": "standard",
                },
                "work": {
                    "lem:a": {
                        "status": "drafted", "scope": "Lemma A.", "updated": "2026-11-26T00:00:00Z",
                        "assembly": {
                            "package": "lean", "module": "Proofs.A", "declaration": "main",
                            "expected": "LemA", "assumes": [],
                            "statements": ["Statements"], "statement_modules": ["Statements.Main"],
                        },
                    },
                    "thm:b": {
                        "status": "drafted", "scope": "Theorem B.", "updated": "2026-11-26T00:00:00Z",
                        "assembly": {
                            "package": "lean", "module": "Proofs.B", "declaration": "main",
                            "expected": "ThmB", "assumes": ["lem:a"],
                            "statements": ["Statements"], "routine": ["Routine"],
                            "witness": "witB", "witness_modules": ["Examples.Main"],
                            "statement_modules": ["Statements.Main"],
                        },
                    },
                },
            }
            # Qualify declarations to match modules.
            (pkg / "Proofs/A.lean").write_text(
                "import Statements.Main\nnamespace ProofsA\ntheorem main : LemA := fun _ => rfl\nend ProofsA\n",
                encoding="utf-8",
            )
            (pkg / "Proofs/B.lean").write_text(
                "import Statements.Main\nimport Routine.Glue\nnamespace ProofsB\n"
                "theorem main (_hA : LemA) : ThmB := fun n _ => add_zero_glue n\nend ProofsB\n",
                encoding="utf-8",
            )
            project["work"]["lem:a"]["assembly"]["declaration"] = "ProofsA.main"
            project["work"]["thm:b"]["assembly"]["declaration"] = "ProofsB.main"
            (root / "project.json").write_text(json.dumps(project, indent=2), encoding="utf-8")

            # Assemble and audit live with Lean 4.33.1.
            with redirect_stdout(io.StringIO()):
                atlas.assemble(root, run_audit=True)

            # Generate hash-locked Challenge.lean & Solution.lean and verify check_only passes.
            harness_report = atlas.generate_challenge_harness(root)
            self.assertTrue(harness_report["packages"]["lean"]["lakefile_configured"])
            atlas.generate_challenge_harness(root, write=False, check_only=True)

            (root / "comparisons.json").write_text("{}\n", encoding="utf-8")
            head = _init_git_commit(root, "initial live build")

            ci_env = {
                "GITHUB_REPOSITORY": "example/phase5-live",
                "GITHUB_SHA": head,
                "GITHUB_RUN_ID": "501",
                "GITHUB_RUN_ATTEMPT": "1",
            }

            # 1. Standard CI live verification on Lean 4.33.1 with full parity.
            with patch.dict(os.environ, ci_env, clear=False):
                std_result = verify_ci.verify(root, offline=True)
            self.assertEqual(std_result["ci_level"], "standard")
            self.assertEqual(std_result["kernels_checked"], ["lean-kernel"])
            self.assertEqual(set(std_result["claims"]), {"lem:a", "thm:b"})
            rec_b = std_result["claims"]["thm:b"]
            self.assertTrue(rec_b["theorem_info"])
            self.assertEqual(rec_b["hygiene"], {"checked": True, "statements_checked": True})
            self.assertEqual(rec_b["statements"], ["Statements"])
            self.assertEqual(rec_b["routine"], ["Routine.Glue"])
            self.assertEqual(rec_b["assumes"], [])
            self.assertEqual(rec_b["hypotheses"], "∃ n, 0 < n")
            self.assertEqual(rec_b["kernels_checked"], ["lean-kernel"])
            self.assertTrue(rec_b["statement_sha256"])

            # 2. Paranoid CI live verification on Lean 4.33.1: real Challenge.lean / Solution.lean build +
            #    cross-environment Lean.importModules kernel type check + #print axioms + executable checker stubs.
            stub_dir = Path(tempfile.mkdtemp(dir=tmp))
            comp_log = stub_dir / "comparator_invoked.json"
            l4c_log = stub_dir / "lean4checker_invoked.txt"

            comp_bin = stub_dir / "fake_comparator.py"
            comp_bin.write_text(
                f"#!{sys.executable}\n"
                "import json, pathlib, sys\n"
                "cfg = json.loads(pathlib.Path(sys.argv[1]).read_text())\n"
                "assert cfg['challenge_module'] == 'Challenge'\n"
                "assert cfg['solution_module'] == 'Solution'\n"
                "assert cfg['theorem_names'] == ['ProofAtlasChallenge.lem_a', 'ProofAtlasChallenge.thm_b']\n"
                f"pathlib.Path({str(comp_log)!r}).write_text(json.dumps(cfg))\n",
                encoding="utf-8",
            )
            comp_bin.chmod(comp_bin.stat().st_mode | stat.S_IXUSR)

            l4c_bin = stub_dir / "fake_lean4checker.py"
            l4c_bin.write_text(
                f"#!{sys.executable}\n"
                "import pathlib, sys\n"
                "assert sys.argv[1] == '--fresh'\n"
                "assert 'Solution' in sys.argv[2:]\n"
                f"pathlib.Path({str(l4c_log)!r}).write_text(' '.join(sys.argv[1:]))\n",
                encoding="utf-8",
            )
            l4c_bin.chmod(l4c_bin.stat().st_mode | stat.S_IXUSR)

            p_env = dict(
                ci_env,
                COMPARATOR_BIN=str(comp_bin),
                LEAN4CHECKER_BIN=str(l4c_bin),
                PROOF_ATLAS_NETWORK_ISOLATED="1",
            )
            with patch.dict(os.environ, p_env, clear=False):
                p_result = verify_ci.verify(root, offline=True, level="paranoid")

            self.assertEqual(p_result["ci_level"], "paranoid")
            self.assertTrue(p_result["network_isolated"])
            self.assertEqual(p_result["kernels_checked"], ["lean-kernel", "comparator", "lean4checker"])
            self.assertTrue(comp_log.is_file())
            self.assertTrue(l4c_log.is_file())
            self.assertEqual(
                p_result["challenge_harness"]["lean"]["targets_checked"],
                ["ProofAtlasChallenge.lem_a", "ProofAtlasChallenge.thm_b"],
            )

            # Build atlas & manifest with the live paranoid CI receipt.
            p_proj = json.loads((root / "project.json").read_text(encoding="utf-8"))
            p_proj["hosting"]["lean_ci_level"] = "paranoid"
            (root / "project.json").write_text(json.dumps(p_proj, indent=2), encoding="utf-8")
            head2 = _init_git_commit(root, "enable paranoid ci")
            p_result["commit"] = head2
            ci_file = root / "lean-verification.json"
            ci_file.write_text(json.dumps(p_result, indent=2), encoding="utf-8")
            with redirect_stdout(io.StringIO()):
                atlas.build(root, ci_receipt=ci_file, commit=head2)
            dash = (root / "dist/progress.html").read_text(encoding="utf-8")
            self.assertIn("Multi-kernel / Comparator", dash)
            rw = atlas.review_work(root, require_ci=True, ci_receipt=ci_file)
            self.assertEqual(rw["ci_pending"], [])

            # 2b. Tampered committed Challenge.lean is rejected in paranoid mode before running checkers.
            orig_challenge = (pkg / "Challenge.lean").read_text(encoding="utf-8")
            (pkg / "Challenge.lean").write_text(orig_challenge + "-- tampered\n", encoding="utf-8")
            head_tamper = _init_git_commit(root, "tamper challenge")
            with patch.dict(os.environ, dict(p_env, GITHUB_SHA=head_tamper), clear=False):
                with self.assertRaisesRegex(ValueError, "committed Challenge.lean differs"):
                    verify_ci.verify(root, offline=True, level="paranoid")
            (pkg / "Challenge.lean").write_text(orig_challenge, encoding="utf-8")

            # 3. CI parity bypass defense: if Prelude.lean imports a local module (even with matching hashes),
            #    verify_ci.py rejects it cleanly.
            (pkg / "Prelude.lean").write_text("import Routine.Glue\n", encoding="utf-8")
            new_prelude_hash = hashlib.sha256((pkg / "Prelude.lean").read_bytes()).hexdigest()
            for cid in ("lem:a", "thm:b"):
                ev_path = root / p_proj["work"][cid]["closure"]["audit"]
                ev_data = json.loads(ev_path.read_text(encoding="utf-8"))
                if "Prelude.lean" in ev_data["checked_inputs"]:
                    ev_data["checked_inputs"]["Prelude.lean"] = new_prelude_hash
                    ev_path.write_text(json.dumps(ev_data, indent=2), encoding="utf-8")
                    p_proj["work"][cid]["checked_inputs"]["lean/Prelude.lean"] = new_prelude_hash
            (root / "project.json").write_text(json.dumps(p_proj, indent=2), encoding="utf-8")
            head3 = _init_git_commit(root, "tamper prelude")
            with patch.dict(os.environ, dict(ci_env, GITHUB_SHA=head3), clear=False):
                with self.assertRaisesRegex(ValueError, r"Prelude\.lean imports local modules \(Routine\.Glue\)"):
                    verify_ci.verify(root, offline=True, level="standard")


if __name__ == "__main__":
    unittest.main()
