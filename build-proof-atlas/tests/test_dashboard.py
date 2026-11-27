from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import atlas


class DashboardCompletion(unittest.TestCase):
    def test_counts_current_closures_and_excludes_conjectures(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder).resolve()

            def source(name, data):
                (root / name).write_bytes(data)
                return {"path": name, "sha256": hashlib.sha256(data).hexdigest()}

            tex = source("paper.tex", (
                r"\begin{theorem}\label{t}Result.\end{theorem}" "\n"
                r"\begin{conjecture}\label{c}Conjecture.\end{conjecture}"
            ).encode())
            pdf = source("paper.pdf", b"test")
            (root / "lean").mkdir()
            checked = source("lean/T.lean", b"theorem result : True := True.intro\n")
            (root / "run.log").write_bytes(b"Built T\n")
            audit = {"expected": "True", "declaration": "result", "axioms": [], "toolchain": "test-pin",
                     "checked_inputs": {"T.lean": checked["sha256"]}}
            (root / "audit.json").write_text(json.dumps(audit), encoding="utf-8")
            closure = {"expected": "True", "declaration": "result", "package": "lean",
                       "audit": "audit.json", "correspondence": "Result."}
            project = {
                "schema_version": 1, "environments": ["theorem", "conjecture"],
                "edition": "test", "title": "Test paper", "tex": [tex], "pdf": pdf,
                "proof_work": {"mode": "paper"}, "hosting": {"decision": "local"},
                "work": {"t": {"status": "closed", "closure": closure, "scope": "Result.",
                               "run_log": "run.log", "checked_inputs": {checked["path"]: checked["sha256"]}}},
            }

            def dashboard(**options):
                (root / "project.json").write_text(json.dumps(project), encoding="utf-8")
                atlas.build(root, **options)
                return (root / "dist/progress.html").read_text(encoding="utf-8")

            complete = "Paper-wide proof work complete"
            with redirect_stdout(io.StringIO()) as log:
                current = dashboard()
            self.assertIn("audited without --statements", log.getvalue())
            self.assertIn("no checked example shows the hypotheses can hold for these closures: t", log.getvalue())
            self.assertIn(atlas.NO_EXAMPLE, current)
            audit["statements"] = ["Statements"]
            audit["hypotheses"] = {"declaration": "holds", "proposition": "True", "axioms": []}
            (root / "audit.json").write_text(json.dumps(audit), encoding="utf-8")
            with redirect_stdout(io.StringIO()) as log:
                current = dashboard()
            self.assertNotIn("audited without --statements", log.getvalue())
            self.assertNotIn("hypotheses can hold", log.getvalue())
            self.assertNotIn(atlas.NO_EXAMPLE, current)
            self.assertIn("1 of 1 stated results closed", current)
            self.assertIn(complete, current)
            self.assertIn("Lean checked", current)
            self.assertNotIn("Machine verified on GitHub", current)
            # The homepage says what the badges cover; the readable views say they are unchecked.
            self.assertIn("What the badges mean", (root / "dist/index.html").read_text(encoding="utf-8"))
            self.assertIn("Explanation, not machine-checked", (root / "dist/explorer.js").read_text(encoding="utf-8"))

            project["hosting"] = {"repository": "https://github.com/example/paper", "lean_ci": "enabled"}
            revision = "a" * 40
            record = {"repository": "example/paper", "commit": revision, "run_id": 123, "attempt": 2,
                      "claims": {"t": dict(audit, audit_sha256=hashlib.sha256((root / "audit.json").read_bytes()).hexdigest(),
                                           hypotheses="True")}}
            path = root / "remote.json"
            path.write_text(json.dumps(record), encoding="utf8")
            options = dict(ci_receipt=path, commit=revision, artifact_id=456)
            verified = dashboard(**options)
            self.assertEqual(verified.count("Machine verified on GitHub"), 1)
            self.assertIn("example/paper/actions/runs/123/attempts/2", verified)
            self.assertIn("example/paper/actions/runs/123/artifacts/456", verified)
            self.assertEqual((root / "dist/logs/lean-verification.json").read_bytes(), path.read_bytes())
            self.assertNotIn("Machine verified on GitHub", dashboard(ci_receipt=path, commit="b"*40))
            # GitHub must have checked the same hypotheses example.
            record["claims"]["t"]["hypotheses"] = "∃ n, n = n"
            path.write_text(json.dumps(record), encoding="utf8")
            self.assertNotIn("Machine verified on GitHub", dashboard(**options))
            record["claims"]["t"]["audit_sha256"] = "0"*64
            path.write_text(json.dumps(record), encoding="utf8")
            self.assertNotIn("Machine verified on GitHub", dashboard(**options))

            # Receipts without a default-value list render as before; with one, both views carry it.
            self.assertNotIn("Lean default values", (root/"dist"/atlas.reviews.review_url("t")).read_text(encoding="utf-8"))
            self.assertIn("Constructive (0 axioms)", (root/"dist"/atlas.reviews.review_url("t")).read_text(encoding="utf-8"))
            audit["defaults"] = [{"constant": "gap", "file": "T.lean", "lines": [1, 1], "construct": "HSub.hSub", "type": "ℕ"}]
            (root / "audit.json").write_text(json.dumps(audit), encoding="utf-8")
            dashboard()
            reader = (root / "dist/proofs/index.html").read_text(encoding="utf-8")
            self.assertIn('"defaults": [{"constant": "gap", "file": "T.lean", "lines": [1, 1], "construct": "HSub.hSub", '
                          '"type": "ℕ", "meaning": "a − b = 0 when b > a", "id":', reader)
            review = (root/"dist"/atlas.reviews.review_url("t")).read_text(encoding="utf-8")
            self.assertIn("<code>HSub.hSub</code> on ℕ in <code>gap</code> (T.lean L1) · a − b = 0 when b &gt; a", review)

            project["proof_work"] = {"mode": "claim", "claim": "t"}
            self.assertNotIn(complete, dashboard())

            project["proof_work"] = {"mode": "paper"}
            (root / checked["path"]).write_bytes(b"-- edited\n")
            stale = dashboard()
            self.assertIn("awaiting recheck", stale)
            self.assertIn("0 of 1 stated results closed", stale)
            self.assertNotIn(complete, stale)

    def test_separable_conditional_assembly_and_unconditional_upgrade(self):
        import author_review as review
        import audit_lean
        from unittest.mock import patch

        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder).resolve()

            def source(name, data):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
                return {"path": name, "sha256": hashlib.sha256(data).hexdigest()}

            tex = source("paper.tex", (
                r"\begin{lemma}\label{lem:a}Lemma A.\end{lemma}" "\n"
                r"\begin{lemma}\label{lem:b}Lemma B.\end{lemma}" "\n"
                r"\begin{theorem}\label{thm:c}Theorem C.\end{theorem}"
            ).encode())
            pdf = source("paper.pdf", b"test")
            stmt_all = source("lean/Statements/All.lean", b"def A : Prop := True\ndef B : Prop := True\ndef C : Prop := True\n")
            source("lean/Proofs/A.lean", b"import Statements.All\ntheorem main : A := trivial\n")
            source("lean/Proofs/C.lean", b"import Statements.All\ntheorem main (_ : A) (_ : B) : C := trivial\n")
            b_stmt_sha = hashlib.sha256(b"B").hexdigest()
            b_stmt_digest = hashlib.sha256(f"Statements.B {b_stmt_sha}\n".encode()).hexdigest()
            source("evidence/b-stmt.json", json.dumps({
                "statement_only": True, "expected": "Statements.B", "axioms": [], "toolchain": "test-pin",
                "statements": ["Statements"], "checked_inputs": {"Statements/All.lean": stmt_all["sha256"]},
                "statement": {"expected": "Statements.B", "sha256": b_stmt_digest,
                              "constants": [{"name": "Statements.B", "file": "Statements/All.lean", "lines": [2, 2], "sha256": b_stmt_sha}]},
                "defaults": [],
            }).encode())
            reader = {
                "schema_version": 1,
                "claims": {
                    "lem:a": {"reference": "Lemma 1"},
                    "lem:b": {"reference": "Lemma 2"},
                    "thm:c": {"reference": "Theorem 3"},
                },
                "dependencies": [
                    {"claim": "thm:c", "prerequisite": "lem:a", "reason": "Step 1"},
                    {"claim": "thm:c", "prerequisite": "lem:b", "reason": "Step 2"},
                ],
            }
            (root / "reader.json").write_text(json.dumps(reader), encoding="utf-8")

            stmt_c_sha = hashlib.sha256(b"C").hexdigest()
            project = {
                "schema_version": 1, "environments": ["lemma", "theorem"],
                "edition": "test", "title": "Conditional test", "tex": [tex], "pdf": pdf,
                "reader": "reader.json",
                "proof_work": {"mode": "paper", "profile": "quick"},
                "hosting": {"decision": "local"},
                "work": {
                    "lem:a": {
                        "status": "drafted", "scope": "Lemma A.", "updated": "2026-11-26T00:00:00Z",
                        "assembly": {"package": "lean", "module": "Proofs.A", "declaration": "Proofs.A.main",
                                     "expected": "Statements.A", "assumes": [], "statement_modules": ["Statements.All"]},
                    },
                    "lem:b": {
                        "status": "attempted", "scope": "Stalled after 8 cycles.", "updated": "2026-11-26T00:00:00Z",
                        "statement_check": {"audit": "evidence/b-stmt.json", "package": "lean", "expected": "Statements.B"},
                    },
                    "thm:c": {
                        "status": "drafted", "scope": "Theorem C.", "updated": "2026-11-26T00:00:00Z",
                        "assembly": {"package": "lean", "module": "Proofs.C", "declaration": "Proofs.C.main",
                                     "expected": "Statements.C", "assumes": ["lem:a", "lem:b"],
                                     "statement_modules": ["Statements.All"]},
                    },
                },
            }
            (root / "project.json").write_text(json.dumps(project), encoding="utf-8")

            # 1. Dry assemble generates Assembly.lean with Lemma 2 as an explicit binder on thm_c.
            dry = atlas.assemble(root)
            assembly_text = (root / "lean/Assembly.lean").read_text(encoding="utf-8")
            self.assertIn("theorem lem_a : _root_.Statements.A :=\n  _root_.Proofs.A.main", assembly_text)
            self.assertIn("theorem thm_c (h_lem_b : _root_.Statements.B) : _root_.Statements.C :=\n  _root_.Proofs.C.main lem_a h_lem_b", assembly_text)
            by_claim = {item["claim"]: item for item in dry["packages"]["lean"]["claims"]}
            self.assertTrue(by_claim["lem:a"]["unconditional"])
            self.assertFalse(by_claim["thm:c"]["unconditional"])
            self.assertEqual(by_claim["thm:c"]["assumes_claims"], ["lem:b"])
            self.assertEqual(by_claim["thm:c"]["assumes_expected"], ["Statements.B"])

            # 2. assemble(run_audit=True) audits both and marks thm:c conditional while lem:a closes.
            def fake_audit(args):
                asm_bytes = (args.package / "Assembly.lean").read_bytes()
                stmt_bytes = (args.package / "Statements/All.lean").read_bytes()
                const_sha = stmt_c_sha if args.expected == "Statements.C" else hashlib.sha256(args.expected.encode()).hexdigest()
                stmt_digest = hashlib.sha256(f"{args.expected} {const_sha}\n".encode()).hexdigest()
                rec = {
                    "declaration": args.declaration, "contract": args.contract, "expected": args.expected,
                    "toolchain": "test-pin", "axioms": [], "axiom_profile": "Constructive (0 axioms)",
                    "external_packages": [], "theorem_info": True, "targets": list(args.target),
                    "input_scope": "module-closure",
                    "checked_inputs": {
                        "Assembly.lean": hashlib.sha256(asm_bytes).hexdigest(),
                        "Statements/All.lean": hashlib.sha256(stmt_bytes).hexdigest(),
                    },
                    "statements": list(args.statements),
                    "hygiene": {"checked": True, "statements_checked": True},
                    "lean_output": f"'{args.declaration}' does not depend on any axioms",
                    "statement": {
                        "expected": args.expected, "sha256": stmt_digest,
                        "constants": [{"name": args.expected, "file": "Statements/All.lean", "lines": [1, 1], "sha256": const_sha}],
                    },
                    "defaults": [],
                }
                if args.assumes:
                    rec["assumes"] = list(args.assumes)
                return rec

            with patch.object(audit_lean, "audit_batch", side_effect=lambda pkg, specs: [fake_audit(s) for s in specs]), redirect_stdout(io.StringIO()):
                atlas.assemble(root, run_audit=True)

            updated = json.loads((root / "project.json").read_text(encoding="utf-8"))
            self.assertEqual(updated["work"]["lem:a"]["status"], "closed")
            self.assertEqual(updated["work"]["thm:c"]["status"], "conditional")
            self.assertEqual(updated["work"]["thm:c"]["assumes"], ["lem:b"])

            dashboard_html = (root / "dist/progress.html").read_text(encoding="utf-8")
            self.assertIn("1 of 3 stated results closed · 1 conditional", dashboard_html)
            self.assertIn("Conditional (assumes Lemma 2)", dashboard_html)
            self.assertNotIn("Paper-wide proof work complete", dashboard_html)
            explorer_html = (root / "dist/proofs/index.html").read_text(encoding="utf-8")
            self.assertIn('"conditional": true', explorer_html)

            # A closed claim with unresolved assumes must be rejected by atlas.build.
            bad_proj = json.loads((root / "project.json").read_text(encoding="utf-8"))
            bad_proj["work"]["thm:c"]["status"] = "closed"
            (root / "project.json").write_text(json.dumps(bad_proj), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "cannot have unresolved assumptions"):
                atlas.build(root)
            (root / "project.json").write_text(json.dumps(updated), encoding="utf-8")

            # Blind comparison + pre-approval on conditional thm:c works and carries over on upgrade!
            pkt_c = review.get_packet(root, "thm:c")
            self.assertTrue(pkt_c["conditional"])
            self.assertFalse(pkt_c["checked"])
            review.save_comparison(root, "thm:c", {
                "bindings": pkt_c["view"]["bindings"], "result": "match",
                "paper_reading": "Theorem C holds.", "lean_reading": "Statements.C holds.",
                "paper_refs": "paper.tex, thm:c", "lean_refs": "Statements.C",
                "analysis": {
                    "summary": "Matches paper.", "scope": "Full theorem.",
                    "cases": [{"case": "C1", "paper": "C", "lean": "Statements.C", "why": "Direct.", "kind": "agrees"}],
                    "advice": "Approve statement.",
                },
            })
            pkt_c = review.get_packet(root, "thm:c")
            review.decide(root, "thm:c", pkt_c["token"], "approve", "Author")
            self.assertTrue(review.get_packet(root, "thm:c")["preapproved"])
            self.assertFalse(review.get_packet(root, "thm:c")["approved"])

            # 3. Close lem:b and reassemble: thm:c upgrades to unconditional closed & pre-approval becomes full approval!
            source("lean/Proofs/B.lean", b"import Statements.All\ntheorem main : B := trivial\n")
            updated["work"]["lem:b"]["assembly"] = {
                "package": "lean", "module": "Proofs.B", "declaration": "Proofs.B.main",
                "expected": "Statements.B", "assumes": [], "statement_modules": ["Statements.All"],
            }
            (root / "project.json").write_text(json.dumps(updated), encoding="utf-8")
            with patch.object(audit_lean, "audit_batch", side_effect=lambda pkg, specs: [fake_audit(s) for s in specs]), redirect_stdout(io.StringIO()):
                atlas.assemble(root, run_audit=True)

            final_proj = json.loads((root / "project.json").read_text(encoding="utf-8"))
            self.assertEqual(final_proj["work"]["lem:b"]["status"], "closed")
            self.assertEqual(final_proj["work"]["thm:c"]["status"], "closed")
            self.assertNotIn("assumes", final_proj["work"]["thm:c"])
            final_asm = (root / "lean/Assembly.lean").read_text(encoding="utf-8")
            self.assertIn("theorem thm_c : _root_.Statements.C :=\n  _root_.Proofs.C.main lem_a lem_b", final_asm)
            self.assertTrue(review.get_packet(root, "thm:c")["approved"])
            final_dash = (root / "dist/progress.html").read_text(encoding="utf-8")
            self.assertIn("3 of 3 stated results closed", final_dash)
            self.assertIn("Paper-wide proof work complete", final_dash)
            self.assertNotIn("Conditional (assumes", final_dash)

            # 4. Cyclic assembly dependencies are rejected cleanly.
            final_proj["work"]["lem:a"]["assembly"]["assumes"] = ["thm:c"]
            (root / "project.json").write_text(json.dumps(final_proj), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "Cyclic assembly dependency"):
                atlas.assemble(root)
