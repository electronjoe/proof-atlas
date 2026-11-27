"""Tests for v0.12.0 lessons: batched audits (#7, #9), witness type (#10), manifest/review-work (#8, #13), paranoid CI (#14, #16, #17, #25)."""
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import atlas
import audit_lean
import author_review as reviews
import hosting
import verify_ci


def _write(root: Path, rel: str, data) -> dict:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = data.encode("utf-8") if isinstance(data, str) else data
    path.write_bytes(raw)
    return {"path": rel, "sha256": hashlib.sha256(raw).hexdigest()}


class LessonsAuditManifestAndCITests(unittest.TestCase):
    def test_latex_escape_greek_and_math_symbols(self):
        escaped = atlas._latex_escape("Space (Ω, μ) with λ̃_j > 0, γ_V*, δ_max, η ≤ 1, ‖x‖ ≈ 0")
        self.assertIn(r"$\Omega$", escaped)
        self.assertIn(r"$\mu$", escaped)
        self.assertIn(r"$\lambda$", escaped)
        self.assertIn(r"$\gamma$", escaped)
        self.assertIn(r"$\delta$", escaped)
        self.assertIn(r"$\eta$", escaped)
        self.assertIn(r"$\le$", escaped)
        self.assertIn(r"$\|$", escaped)
        self.assertIn(r"$\approx$", escaped)
        self.assertNotIn("Ω", escaped)
        self.assertNotIn("μ", escaped)

    def test_closed_with_difference_and_classical_noncomputable_summary(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            tex = _write(root, "paper.tex", (
                "\\begin{thm}[Repaired Theorem]\\label{thm:repaired}\n"
                "Delay bound holds.\n"
                "\\end{thm}\n"
            ))
            pdf = _write(root, "paper.pdf", b"%PDF-1.4\n")
            stmt = _write(root, "lean/Statements/Repaired.lean", "def Repaired : Prop := True\n")
            prf = _write(root, "lean/Proofs/Repaired.lean", "import Statements.Repaired\ntheorem main : Repaired := trivial\n")
            _write(root, "lean/lean-toolchain", "leanprover/lean4:v4.33.1\n")
            _write(root, "lean/lakefile.toml", 'name = "Demo"\n[[lean_lib]]\nname = "Statements"\n[[lean_lib]]\nname = "Proofs"\n')
            _write(root, "lean/lake-manifest.json", '{"packagesDir": ".lake/packages", "packages": []}\n')
            _write(root, "run.log", "OK\n")

            stmt_sha = hashlib.sha256(b"Statements.Repaired").hexdigest()
            audit_obj = {
                "declaration": "Proofs.Repaired.main",
                "contract": "Contract.lean",
                "expected": "Statements.Repaired",
                "toolchain": "leanprover/lean4:v4.33.1",
                "axioms": ["propext", "Classical.choice", "Quot.sound"],
                "axiom_profile": "Standard classical axioms (Classical.choice, Quot.sound, propext)",
                "external_packages": [],
                "theorem_info": True,
                "targets": ["Proofs.Repaired"],
                "statements": ["Statements"],
                "checked_inputs": {
                    "Statements/Repaired.lean": stmt["sha256"],
                    "Proofs/Repaired.lean": prf["sha256"],
                },
                "statement": {
                    "expected": "Statements.Repaired",
                    "sha256": stmt_sha,
                    "constants": [
                        {"name": "Real.log", "file": "Statements/Repaired.lean", "lines": [1, 1], "sha256": stmt_sha, "noncomputable": True},
                        {"name": "Real.sqrt", "file": "Statements/Repaired.lean", "lines": [1, 1], "sha256": stmt_sha, "noncomputable": True},
                        {"name": "MeasureTheory.integral", "file": "Statements/Repaired.lean", "lines": [1, 1], "sha256": stmt_sha, "noncomputable": True},
                        {"name": "Set.Finite.toFinset", "file": "Statements/Repaired.lean", "lines": [1, 1], "sha256": stmt_sha, "noncomputable": True},
                    ],
                },
                "defaults": [],
                "hypotheses": {"declaration": "Examples.wit", "proposition": "True", "axioms": []},
            }
            _write(root, "evidence/repaired.json", json.dumps(audit_obj, indent=2))
            project = {
                "schema_version": 1,
                "title": "Repaired Study",
                "edition": "arXiv:1008.4895v2",
                "revision": "1008.4895v2",
                "publication": "https://arxiv.org/abs/1008.4895v2",
                "tex": [tex],
                "pdf": pdf,
                "environments": ["thm"],
                "reader": "reader.json",
                "hosting": {"decision": "local"},
                "work": {
                    "thm:repaired": {
                        "status": "closed",
                        "distilled": True,
                        "scope": "Formalizes repaired statement with explicit positivity guard.",
                        "step": "Closed",
                        "next": "Done",
                        "updated": "2026-11-27T00:00:00Z",
                        "run_log": "run.log",
                        "checked_inputs": {
                            "lean/Statements/Repaired.lean": stmt["sha256"],
                            "lean/Proofs/Repaired.lean": prf["sha256"],
                        },
                        "closure": {
                            "package": "lean",
                            "expected": "Statements.Repaired",
                            "declaration": "Proofs.Repaired.main",
                            "audit": "evidence/repaired.json",
                            "correspondence": "Repaired constant and positivity guard.",
                        },
                    }
                },
            }
            _write(root, "project.json", json.dumps(project, indent=2))
            _write(root, "reader.json", json.dumps({
                "schema_version": 1,
                "claims": {
                    "thm:repaired": {
                        "reference": "Theorem 4",
                        "summary": "Bounded delay under $V \\ge 1$.",
                        "sketch": "Combine Theorems 1–3 via a sample-path bound.",
                    }
                },
                "dependencies": [],
            }, indent=2))

            claims = atlas.manuscript_claims(root, project)
            b = reviews.bindings(project, claims[0], audit_obj)
            comp = {
                "thm:repaired": {
                    "bindings": b,
                    "paper_reading": "Paper theorem without explicit positivity guard.",
                    "lean_reading": "Lean theorem adds positivity guard.",
                    "paper_refs": "Section VI-C",
                    "lean_refs": "Statements/Repaired.lean",
                    "result": "difference",
                    "issue": "Adds missing positivity guard on arrival rate.",
                    "actor": "Author",
                    "next": "Confirm repaired statement.",
                    "analysis": {
                        "summary": "One missing positivity guard repaired.",
                        "scope": "Classical probability theorem.",
                        "advice": "Adopt manuscript edit.",
                        "suggested_feedback": "Confirm positivity guard.",
                        "cases": [{
                            "case": "C1 (Positivity)",
                            "kind": "added hypothesis",
                            "paper": "Omitted",
                            "lean": "Explicit positivity",
                            "why": "Needed to avoid division by zero.",
                        }],
                    },
                }
            }
            _write(root, "comparisons.json", json.dumps(comp, indent=2))

            rw = atlas.review_work(root)
            # #13: Counted under closed_with_difference, NOT open!
            self.assertEqual(rw["summary"]["headline"]["closed_with_difference"], 1)
            self.assertEqual(rw["summary"]["headline"]["open"], 0)
            self.assertEqual(rw["summary"]["headline"]["unconditionally_closed"], 0)

            man = atlas.manifest(root)
            self.assertIn("Closed (with difference)", man["markdown"])
            self.assertIn("1 closed with recorded difference", man["latex"])
            # #8: Classical noncomputable helpers summarized concisely without dumping all 4 names into LaTeX.
            self.assertIn("uses classical real/measure definitions: 4 noncomputable constants", man["latex"])
            self.assertNotIn("MeasureTheory.integral", man["latex"])

    def test_audit_lean_batch_cli_and_expected_witness_proposition(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            _write(root, "lean-toolchain", "leanprover/lean4:v4.33.1\n")
            _write(root, "lakefile.toml", 'name = "Demo"\n[[lean_lib]]\nname = "Statements"\n')
            _write(root, "lake-manifest.json", '{"packagesDir": ".lake/packages", "packages": []}\n')
            _write(root, "Statements/A.lean", "def A : Prop := ∀ n : Nat, 0 < n → True\n")
            _write(root, "Statements/B.lean", "def B : Prop := ∀ m : Nat, 0 < m → True\n")
            _write(root, "ContractA.lean", "import Statements.A\n")
            _write(root, "ContractB.lean", "import Statements.B\n")

            build_calls = []

            def fake_run(cmd, cwd, env, log):
                build_calls.append(list(cmd))

            def fake_module_inputs(lake, pkg_root, env, targets, contract_path):
                base = {"lean-toolchain", "lakefile.toml", "lake-manifest.json", contract_path}
                if contract_path == "ContractA.lean":
                    return (base | {"Statements/A.lean"}, ["+Statements.A"])
                return (base | {"Statements/B.lean"}, ["+Statements.B"])

            def fake_sub_run(cmd, *, input=b"", **kwargs):
                text = input.decode("utf-8")
                if '"A"' in text:
                    out = (
                        "'A' does not depend on any axioms\n"
                        'PROOF-ATLAS-EXPECTED-WITNESS {"needed": "∃ n, 0 < n"}\n'
                    )
                else:
                    out = (
                        "'B' does not depend on any axioms\n"
                        'PROOF-ATLAS-EXPECTED-WITNESS {"needed": "∃ m, 0 < m"}\n'
                    )
                return subprocess.CompletedProcess(cmd, 0, out.encode("utf-8"), b"")

            def fake_stmt_record(lake, pkg_root, env, contract_path, expected, *, local_modules=None):
                sha = hashlib.sha256(expected.encode()).hexdigest()
                return ({"expected": expected, "sha256": sha, "constants": []}, [])

            batch_file = root / "batch.json"
            out_a = root / "ev/a.json"
            out_b = root / "ev/b.json"
            batch_file.write_text(json.dumps({
                "defaults": {"statements": ["Statements"]},
                "claims": [
                    {"contract": "ContractA.lean", "expected": "A", "output": str(out_a)},
                    {"contract": "ContractB.lean", "expected": "B", "output": str(out_b)},
                ],
            }), encoding="utf-8")

            args = SimpleNamespace(
                package=root, batch=batch_file, statement_only=True,
                statements=[], routine=[], target=[],
            )
            with patch.object(audit_lean, "select_lake", return_value=["lake"]), \
                 patch.object(audit_lean, "module_inputs", side_effect=fake_module_inputs), \
                 patch.object(audit_lean, "check_routine", return_value=[]), \
                 patch.object(audit_lean, "run", side_effect=fake_run), \
                 patch.object(audit_lean.subprocess, "run", side_effect=fake_sub_run), \
                 patch.object(audit_lean, "check_statements", return_value=["Statements.A"]), \
                 patch.object(audit_lean, "statement_record", side_effect=fake_stmt_record), \
                 patch.object(sys, "stderr", io.StringIO()):
                written = audit_lean.run_batch_cli(args)

            # Single batched Lake build for both Gate 1 claims (#7).
            self.assertEqual(len(build_calls), 1)
            self.assertEqual(len(written), 2)
            rec_a = json.loads(out_a.read_text(encoding="utf-8"))
            rec_b = json.loads(out_b.read_text(encoding="utf-8"))
            # #10: expected_witness_proposition recorded automatically in --statement-only receipts.
            self.assertEqual(rec_a["expected_witness_proposition"], "∃ n, 0 < n")
            self.assertEqual(rec_b["expected_witness_proposition"], "∃ m, 0 < m")

            # Refuses to overwrite existing batch outputs up front.
            with self.assertRaises(FileExistsError):
                audit_lean.run_batch_cli(args)

    def test_assemble_audit_batches_via_audit_batch(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            tex = _write(root, "paper.tex", (
                "\\begin{thm}[One]\\label{t1}First.\\end{thm}\n"
                "\\begin{thm}[Two]\\label{t2}Second.\\end{thm}\n"
            ))
            pdf = _write(root, "paper.pdf", b"%PDF-1.4\n")
            _write(root, "lean/Statements/S.lean", "def S1 : Prop := True\ndef S2 : Prop := True\n")
            _write(root, "lean/Proofs/P1.lean", "import Statements.S\ntheorem p1 : S1 := trivial\n")
            _write(root, "lean/Proofs/P2.lean", "import Statements.S\ntheorem p2 (_ : S1) : S2 := trivial\n")
            _write(root, "lean/lakefile.toml", 'name = "Demo"\n[[lean_lib]]\nname = "Statements"\n[[lean_lib]]\nname = "Proofs"\n[[lean_lib]]\nname = "Assembly"\n')
            project = {
                "schema_version": 1,
                "title": "Batch Assemble",
                "edition": "Local",
                "revision": "1",
                "tex": [tex],
                "pdf": pdf,
                "environments": ["thm"],
                "hosting": {"decision": "local"},
                "work": {
                    "t1": {"status": "attempted", "assembly": {"package": "lean", "module": "Proofs.P1", "declaration": "p1", "expected": "S1", "assumes": [], "statement_modules": ["Statements.S"]}},
                    "t2": {"status": "attempted", "assembly": {"package": "lean", "module": "Proofs.P2", "declaration": "p2", "expected": "S2", "assumes": ["t1"], "statement_modules": ["Statements.S"]}},
                },
            }
            _write(root, "project.json", json.dumps(project, indent=2))

            batch_calls = []

            def fake_audit_batch(pkg_root, specs):
                batch_calls.append(len(specs))
                return [
                    {
                        "declaration": s.declaration,
                        "expected": s.expected,
                        "axioms": [],
                        "statements": ["Statements"],
                        "checked_inputs": {"Statements/S.lean": "abc"},
                        "lean_output": "ok",
                    }
                    for s in specs
                ]

            with patch.object(audit_lean, "audit_batch", side_effect=fake_audit_batch), \
                 patch.object(atlas, "build_local"):
                atlas.assemble(root, run_audit=True)
            # #9: Called audit_batch ONCE with 2 specs instead of 2 sequential audit() calls!
            self.assertEqual(batch_calls, [2])

    def test_verify_ci_builtin_leanchecker_v4_28_plus(self):
        # #14: Built-in leanchecker supported for >= v4.28.0, not < v4.28.0.
        self.assertFalse(verify_ci.supports_builtin_leanchecker("leanprover/lean4:v4.27.0"))
        self.assertTrue(verify_ci.supports_builtin_leanchecker("leanprover/lean4:v4.28.0"))
        self.assertTrue(verify_ci.supports_builtin_leanchecker("leanprover/lean4:v4.33.1"))

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            fake_prefix = root / "sysroot"
            bin_path = fake_prefix / "bin" / "leanchecker"
            bin_path.parent.mkdir(parents=True)
            bin_path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")

            calls = []

            def fake_run(cmd, **kwargs):
                calls.append(cmd)
                if "--print-prefix" in cmd:
                    return subprocess.CompletedProcess(cmd, 0, str(fake_prefix) + "\n", "")
                return subprocess.CompletedProcess(cmd, 0, b"ok", b"")

            with patch.dict("os.environ", {}, clear=False), \
                 patch.object(verify_ci.shutil, "which", return_value=None), \
                 patch.object(verify_ci, "_manifest_has_package", return_value=False), \
                 patch.object(verify_ci.subprocess, "run", side_effect=fake_run):
                kernels = verify_ci.run_lean4checker(root, ["Solution"], {}, ["lake"])
            self.assertEqual(kernels, ["leanchecker"])
            self.assertTrue(any(str(bin_path) in c for c in calls))

    def test_challenge_configure_lakefile_and_github_pages_yml(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            tex = _write(root, "paper.tex", "\\begin{thm}[T]\\label{t}Body.\\end{thm}\n")
            pdf = _write(root, "paper.pdf", b"%PDF-1.4\n")
            stmt = _write(root, "lean/Statements/T.lean", "def T : Prop := True\n")
            prf = _write(root, "lean/Proofs/T.lean", "import Statements.T\ntheorem main : T := trivial\n")
            _write(root, "lean/lakefile.toml", 'name = "Demo"\n[[lean_lib]]\nname = "Statements"\n[[lean_lib]]\nname = "Proofs"\n')
            _write(root, "evidence/t.json", json.dumps({
                "expected": "T",
                "declaration": "main",
                "targets": ["Proofs.T"],
                "statements": ["Statements"],
                "statement": {"sha256": "deadbeef", "constants": [{"name": "T", "file": "Statements/T.lean"}]},
            }))
            _write(root, "project.json", json.dumps({
                "schema_version": 1,
                "title": "Demo",
                "edition": "Local",
                "revision": "1",
                "tex": [tex],
                "pdf": pdf,
                "environments": ["thm"],
                "work": {
                    "t": {
                        "status": "closed",
                        "closure": {"package": "lean", "expected": "T", "declaration": "main", "audit": "evidence/t.json"},
                    }
                },
            }))

            # Without --configure-lakefile, warns clearly.
            err = io.StringIO()
            with patch.object(sys, "stderr", err):
                rep1 = atlas.generate_challenge_harness(root, write=True, configure_lakefile=False)
            self.assertFalse(rep1["packages"]["lean"]["lakefile_configured"])
            self.assertIn("--configure-lakefile", err.getvalue())

            # With --configure-lakefile, appends Challenge and Solution stanzas.
            err2 = io.StringIO()
            with patch.object(sys, "stderr", err2):
                rep2 = atlas.generate_challenge_harness(root, write=True, configure_lakefile=True)
            self.assertTrue(rep2["packages"]["lean"]["lakefile_configured"])
            self.assertEqual(rep2["packages"]["lean"]["lakefile_libs_added"], ["Challenge", "Solution"])
            toml_text = (root / "lean/lakefile.toml").read_text(encoding="utf-8")
            self.assertIn('name = "Challenge"', toml_text)
            self.assertIn('name = "Solution"', toml_text)

        # #17 & #25: Verify github-pages.yml runs manifest and accepts anchor attributes.
        pages_yml = (Path(__file__).resolve().parents[1] / "references/github-pages.yml").read_text(encoding="utf-8")
        self.assertIn('atlas.py manifest . "${args[@]}"', pages_yml)
        self.assertIn('"VERIFICATION.md"', pages_yml)
        self.assertIn(r'<a\b[^>]*\bhref="manuscript\.pdf"', pages_yml)
        # Verify the regex matches anchors with extra attributes like target/rel/class.
        caption = 'Author (<a class="pub" href="https://arxiv.org/abs/1008.4895v2" target="_blank" rel="noopener">arXiv:1008.4895v2</a>) · <a class="pdf" href="manuscript.pdf" target="_blank">PDF</a>'
        self.assertIsNotNone(re.search(r'<a\b[^>]*\bhref="manuscript\.pdf"', caption))
        self.assertIsNotNone(re.search(r'<a\b[^>]*\bhref="' + re.escape("https://arxiv.org/abs/1008.4895v2") + r'"', caption))


if __name__ == "__main__":
    unittest.main()
