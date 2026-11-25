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
import author_review as review


class Phase3aGroundingTwoHomesDistillation(unittest.TestCase):
    def _write_source(self, root, name, data):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        raw = data.encode("utf-8") if isinstance(data, str) else data
        path.write_bytes(raw)
        return {"path": name, "sha256": hashlib.sha256(raw).hexdigest()}

    def _make_stmt(self, expected, line, file="Statements/All.lean"):
        sha = hashlib.sha256(expected.encode("utf-8")).hexdigest()
        return {
            "expected": expected,
            "sha256": hashlib.sha256(f"{expected} {sha}\n".encode("utf-8")).hexdigest(),
            "constants": [{"name": expected, "file": file, "lines": [line, line], "sha256": sha}],
        }

    def test_kernel_extracted_claim_dag_grounding_and_transitive_reduction(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder).resolve()
            tex = self._write_source(root, "paper.tex", (
                r"\begin{lemma}\label{lem:a}Base lemma A.\end{lemma}" "\n"
                r"\begin{lemma}\label{lem:b}Intermediate lemma B.\end{lemma}" "\n"
                r"\begin{lemma}\label{lem:c}Paper-cited lemma C.\end{lemma}" "\n"
                r"\begin{lemma}\label{lem:d}Hidden Lean prerequisite D.\end{lemma}" "\n"
                r"\begin{lemma}\label{lem:e}Statement-only prerequisite E.\end{lemma}" "\n"
                r"\begin{theorem}\label{thm:main}Main theorem.\end{theorem}" "\n"
                r"\begin{corollary}\label{cor:open}Open corollary.\end{corollary}" "\n"
            ))
            pdf = self._write_source(root, "paper.pdf", b"%PDF-1.4\n")
            stmt = self._write_source(root, "lean/Statements/All.lean", (
                "def A : Prop := True\n"
                "def B : Prop := True\n"
                "def C : Prop := True\n"
                "def D : Prop := True\n"
                "def E : Prop := True\n"
                "def Main : Prop := True\n"
                "def OpenCor : Prop := True\n"
            ))
            prf_a = self._write_source(root, "lean/Proofs/A.lean", "theorem main : A := trivial\n")
            prf_b = self._write_source(root, "lean/Proofs/B.lean", "theorem main : B := trivial\n")
            prf_d = self._write_source(root, "lean/Proofs/D.lean", "theorem main : D := trivial\n")
            prf_m = self._write_source(root, "lean/Proofs/Main.lean", "theorem main : Main := trivial\n")
            self._write_source(root, "run.log", "OK\n")

            def write_audit(fname, expected, decl, prf_info, line, *, used_thms=(), used_stmts=(), loc=25):
                rec = {
                    "expected": expected, "declaration": decl,
                    "axioms": [], "axiom_profile": "Constructive (0 axioms)",
                    "toolchain": "leanprover/lean4:v4.24.0", "statements": ["Statements"],
                    "checked_inputs": {"Statements/All.lean": stmt["sha256"], prf_info["path"].removeprefix("lean/"): prf_info["sha256"]},
                    "statement": self._make_stmt(expected, line),
                    "defaults": [],
                    "used_local_theorems": list(used_thms),
                    "used_local_statements": list(used_stmts),
                    "reachable_local_defs": 2,
                    "reachable_local_theorems": len(used_thms),
                    "checked_lean_loc": loc,
                }
                self._write_source(root, fname, json.dumps(rec))

            write_audit("evidence/a.json", "Statements.A", "Proofs.A.main", prf_a, 1)
            write_audit("evidence/b.json", "Statements.B", "Proofs.B.main", prf_b, 2,
                        used_thms=["Proofs.A.main"], used_stmts=["Statements.A"])
            write_audit("evidence/d.json", "Statements.D", "Proofs.D.main", prf_d, 4)
            # thm:main transitively reaches A via B (should be reduced away as non-redundant),
            # uses B (both), does NOT use C (paper_only), uses D via theorem (lean_only),
            # and references Statements.E via .Statement (lean_only)!
            write_audit(
                "evidence/main.json", "Statements.Main", "Proofs.Main.main", prf_m, 6,
                used_thms=["Proofs.B.main", "Proofs.A.main", "Proofs.D.main", "Routine.Glue.helper"],
                used_stmts=["Statements.B", "Statements.A", "Statements.E"],
                loc=140,
            )
            e_stmt_audit = {
                "statement_only": True, "expected": "Statements.E", "axioms": [],
                "toolchain": "leanprover/lean4:v4.24.0", "statements": ["Statements"],
                "checked_inputs": {"Statements/All.lean": stmt["sha256"]},
                "statement": self._make_stmt("Statements.E", 5),
                "defaults": [],
            }
            self._write_source(root, "evidence/e-stmt.json", json.dumps(e_stmt_audit))

            reader = {
                "schema_version": 1,
                "claims": {
                    "lem:a": {"reference": "Lemma 1"},
                    "lem:b": {"reference": "Lemma 2"},
                    "lem:c": {"reference": "Lemma 3"},
                    "lem:d": {"reference": "Lemma 4"},
                    "lem:e": {"reference": "Lemma 5"},
                    "thm:main": {"reference": "Theorem 6"},
                    "cor:open": {"reference": "Corollary 7"},
                },
                "dependencies": [
                    {"claim": "lem:b", "prerequisite": "lem:a", "reason": "B invokes A"},
                    {"claim": "thm:main", "prerequisite": "lem:b", "reason": "Main invokes B"},
                    {"claim": "thm:main", "prerequisite": "lem:c", "reason": "Paper proof cites C"},
                    {"claim": "cor:open", "prerequisite": "thm:main", "reason": "Corollary of main"},
                ],
            }
            self._write_source(root, "reader.json", json.dumps(reader))

            def closed_work(expected, decl, audit_path, prf_info):
                return {
                    "status": "closed", "scope": f"Proof of {expected}.", "run_log": "run.log",
                    "checked_inputs": {"lean/Statements/All.lean": stmt["sha256"], prf_info["path"]: prf_info["sha256"]},
                    "closure": {"package": "lean", "expected": expected, "declaration": decl,
                                "audit": audit_path, "correspondence": f"Matches {expected}."},
                }

            project = {
                "schema_version": 1, "environments": ["lemma", "theorem", "corollary"],
                "edition": "v1", "title": "DAG Grounding Test", "tex": [tex], "pdf": pdf,
                "reader": "reader.json", "proof_work": {"mode": "paper", "profile": "quick"},
                "hosting": {"decision": "local"},
                "work": {
                    "lem:a": closed_work("Statements.A", "Proofs.A.main", "evidence/a.json", prf_a),
                    "lem:b": closed_work("Statements.B", "Proofs.B.main", "evidence/b.json", prf_b),
                    "lem:d": closed_work("Statements.D", "Proofs.D.main", "evidence/d.json", prf_d),
                    "lem:e": {
                        "status": "drafted", "scope": "Drafted E.", "updated": "2026-11-26T00:00:00Z",
                        "statement_check": {"audit": "evidence/e-stmt.json", "package": "lean", "expected": "Statements.E"},
                    },
                    "thm:main": closed_work("Statements.Main", "Proofs.Main.main", "evidence/main.json", prf_m),
                },
            }
            self._write_source(root, "project.json", json.dumps(project))

            # Mark lem:d (a Lean-only prerequisite of thm:main) with needs_author_confirmation
            # to verify confirmation propagation also follows kernel-extracted Lean-only edges!
            pkt_d = review.get_packet(root, "lem:d")
            review.save_comparison(root, "lem:d", {
                "bindings": pkt_d["view"]["bindings"], "result": "match",
                "needs_author_confirmation": True,
                "paper_reading": "D holds.", "lean_reading": "Statements.D fixes strict reading.",
                "paper_refs": "paper.tex, lem:d", "lean_refs": "Statements.D",
                "analysis": {
                    "summary": "Quick reading.", "scope": "Strict.",
                    "cases": [{"case": "C1", "paper": "Implicit", "lean": "Explicit", "why": "Quick choice.",
                               "kind": "chosen reading", "needs_author_confirmation": True}],
                    "advice": "Confirm reading.",
                },
            })

            with redirect_stdout(io.StringIO()):
                atlas.build(root)

            # Parse embedded atlas payload from dist/proofs/index.html.
            html = (root / "dist/proofs/index.html").read_text(encoding="utf-8")
            marker = '<script id="atlas-data" type="application/json">'
            start = html.index(marker) + len(marker)
            end = html.index("</script>", start)
            payload = json.loads(html[start:end].replace(r"\u003c", "<"))

            edges_by_pair = {(e["claim"], e["prerequisite"]): e for e in payload["dependencies"]}
            self.assertEqual(edges_by_pair[("lem:b", "lem:a")]["grounding"], "both")
            self.assertEqual(edges_by_pair[("thm:main", "lem:b")]["grounding"], "both")
            self.assertEqual(edges_by_pair[("thm:main", "lem:c")]["grounding"], "paper_only")
            self.assertEqual(edges_by_pair[("cor:open", "thm:main")]["grounding"], "paper")
            self.assertEqual(edges_by_pair[("thm:main", "lem:d")]["grounding"], "lean_only")
            self.assertEqual(edges_by_pair[("thm:main", "lem:d")]["lean_refs"], ["Proofs.D.main"])
            self.assertEqual(edges_by_pair[("thm:main", "lem:e")]["grounding"], "lean_only")
            self.assertEqual(edges_by_pair[("thm:main", "lem:e")]["lean_refs"], ["Statements.E"])
            # Transitive reduction: thm:main -> lem:a is already implied via lem:b, so no redundant lean_only edge!
            self.assertNotIn(("thm:main", "lem:a"), edges_by_pair)

            self.assertEqual(payload["dag_grounding"], {"both": 2, "paper_only": 1, "lean_only": 2, "paper": 1})

            by_cid = {c["id"]: c for c in payload["claims"]}
            main_ld = by_cid["thm:main"]["lean_dependencies"]
            self.assertEqual([x["id"] for x in main_ld["both"]], ["lem:b"])
            self.assertEqual([x["id"] for x in main_ld["paper_only"]], ["lem:c"])
            self.assertEqual([x["id"] for x in main_ld["lean_only"]], ["lem:d", "lem:e"])
            self.assertIn("Routine.Glue.helper", main_ld["used_local_theorems"])

            # Needs author confirmation propagated from Lean-only prerequisite lem:d to thm:main!
            via_ids = [x["id"] for x in by_cid["thm:main"]["verification"]["needs_author_confirmation_via"]]
            self.assertIn("lem:d", via_ids)

            # graph.js & VERIFICATION.md surface all three grounding categories.
            graph_js = (root / "dist/graph.js").read_text(encoding="utf-8")
            self.assertIn("Used in both paper & Lean proof", graph_js)
            self.assertIn("Paper-only dependency", graph_js)
            self.assertIn("Lean-only prerequisite", graph_js)

            manifest_res = atlas.manifest(root)
            self.assertEqual(manifest_res["dag_grounding"], {"both": 2, "paper_only": 1, "lean_only": 2, "paper": 1})
            self.assertIn("## Kernel-Extracted Dependency Grounding", manifest_res["markdown"])
            self.assertIn("**Used in both paper & Lean proof:** 2", manifest_res["markdown"])
            self.assertIn("**Paper-only dependency (Lean proved independently):** 1", manifest_res["markdown"])
            self.assertIn("**Lean-only prerequisite:** 2", manifest_res["markdown"])

    def test_two_homes_basis_supplement_md_badges_review_and_manifest(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder).resolve()
            tex = self._write_source(root, "paper.tex", (
                r"\begin{theorem}[Main paper result]\label{thm:paper}Main theorem with paper proof.\end{theorem}" "\n"
                r"\begin{remark}[Positivity remark]\label{rem:supplied}Unproved remark supplied in Lean.\end{remark}" "\n"
                r"\begin{proposition}\label{prop:supplied_cond}Skipped step proved conditionally.\end{proposition}" "\n"
                r"\begin{lemma}\label{lem:aligned}Aligned proof lemma.\end{lemma}" "\n"
                r"\begin{lemma}\label{lem:lean_route}Alternative Lean route lemma.\end{lemma}" "\n"
            ))
            pdf = self._write_source(root, "paper.pdf", b"%PDF-1.4\n")
            stmt = self._write_source(root, "lean/Statements/All.lean", (
                "def P1 : Prop := True\n"
                "def R2 : Prop := True\n"
                "def P3 : Prop := True\n"
                "def L4 : Prop := True\n"
                "def L5 : Prop := True\n"
            ))
            prf1 = self._write_source(root, "lean/Proofs/P1.lean", "theorem main : P1 := trivial\n")
            prf2 = self._write_source(root, "lean/Proofs/R2.lean", "theorem main : R2 := trivial\n")
            prf3 = self._write_source(root, "lean/Proofs/P3.lean", "theorem main (_ : L4) : P3 := trivial\n")
            prf5 = self._write_source(root, "lean/Proofs/L5.lean", "theorem main : L5 := trivial\n")
            self._write_source(root, "run.log", "OK\n")
            self._write_source(root, "lamport/rem_supplied.md", (
                "**Step 1.** Unfold the remark's implicit positivity assumption.\n\n"
                "**Step 2.** Apply the monotonicity bound to conclude the remark.\n"
            ))

            def write_audit(fname, expected, decl, prf_info, line, *, assumes=(), loc=42, defs=3, thms=2):
                rec = {
                    "expected": expected, "declaration": decl,
                    "axioms": [], "axiom_profile": "Constructive (0 axioms)",
                    "toolchain": "leanprover/lean4:v4.24.0", "statements": ["Statements"],
                    "checked_inputs": {"Statements/All.lean": stmt["sha256"], prf_info["path"].removeprefix("lean/"): prf_info["sha256"]},
                    "statement": self._make_stmt(expected, line),
                    "hypotheses": {"declaration": "Examples.wit", "proposition": "True", "axioms": []},
                    "defaults": [],
                    "checked_lean_loc": loc,
                    "reachable_local_defs": defs,
                    "reachable_local_theorems": thms,
                    **({"assumes": list(assumes)} if assumes else {}),
                }
                return self._write_source(root, fname, json.dumps(rec))

            write_audit("evidence/p1.json", "Statements.P1", "Proofs.P1.main", prf1, 1, loc=30, defs=1, thms=0)
            r2_audit = write_audit("evidence/r2.json", "Statements.R2", "Proofs.R2.main", prf2, 2, loc=55, defs=2, thms=1)
            write_audit("evidence/p3.json", "Statements.P3", "Proofs.P3.main", prf3, 3, assumes=["Statements.L4"], loc=20, defs=2, thms=0)
            write_audit("evidence/l5.json", "Statements.L5", "Proofs.L5.main", prf5, 5, loc=80, defs=4, thms=3)

            reader = {
                "schema_version": 1,
                "claims": {
                    "thm:paper": {"reference": "Theorem 1", "basis": "paper"},
                    "rem:supplied": {
                        "reference": "Remark 2",
                        "basis": "supplied",
                        "page": 4,
                        "summary": "Positivity holds directly from the structural invariant.",
                        "sketch": "Combine monotonicity with the lower bound.",
                        "lamport": "lamport/rem_supplied.md",
                    },
                    "prop:supplied_cond": {
                        "reference": "Proposition 3",
                        "basis": "paper",  # Overridden by work[...].basis = 'supplied'
                        "structured": "1. Assume Lemma 4.\n2. Conclude Proposition 3.",
                    },
                    "lem:aligned": {"reference": "Lemma 4", "basis": "aligned"},
                    "lem:lean_route": {"reference": "Lemma 5", "basis": "lean"},
                },
                "dependencies": [],
            }
            self._write_source(root, "reader.json", json.dumps(reader))

            def closed_work(expected, decl, audit_path, prf_info, **extra):
                return {
                    "status": "closed", "scope": f"Proof of {expected}.", "run_log": "run.log",
                    "checked_inputs": {"lean/Statements/All.lean": stmt["sha256"], prf_info["path"]: prf_info["sha256"]},
                    "closure": {"package": "lean", "expected": expected, "declaration": decl,
                                "audit": audit_path, "correspondence": f"Matches {expected}."},
                    **extra,
                }

            project = {
                "schema_version": 1, "environments": ["theorem", "remark", "proposition", "lemma"],
                "edition": "arXiv:2611.88888v1", "title": "Two Homes Study",
                "authors": ["Alice Author"], "tex": [tex], "pdf": pdf, "reader": "reader.json",
                "proof_work": {"mode": "paper", "profile": "thorough"},
                "hosting": {
                    "decision": "github", "repository": "https://github.com/example/two-homes",
                    "site": "https://example.github.io/two-homes/", "lean_ci": "enabled",
                },
                "work": {
                    "thm:paper": closed_work("Statements.P1", "Proofs.P1.main", "evidence/p1.json", prf1, distilled=True),
                    "rem:supplied": closed_work("Statements.R2", "Proofs.R2.main", "evidence/r2.json", prf2, distilled=True),
                    "prop:supplied_cond": {
                        "status": "conditional", "basis": "supplied", "assumes": ["lem:aligned"],
                        "scope": "Supplied conditional argument.", "run_log": "run.log",
                        "checked_inputs": {"lean/Statements/All.lean": stmt["sha256"], prf3["path"]: prf3["sha256"]},
                        "closure": {"package": "lean", "expected": "Statements.P3", "declaration": "Proofs.P3.main",
                                    "audit": "evidence/p3.json", "correspondence": "Matches Proposition 3 assuming Lemma 4."},
                    },
                    "lem:lean_route": closed_work("Statements.L5", "Proofs.L5.main", "evidence/l5.json", prf5, distilled=False),
                },
            }
            self._write_source(root, "project.json", json.dumps(project))

            # Attach CI receipt verifying rem:supplied so we verify CI badge doesn't mask Two Homes provenance.
            commit = "d" * 40
            r2_json = json.loads((root / "evidence/r2.json").read_text(encoding="utf-8"))
            ci_path = root / "ci.json"
            ci_path.write_text(json.dumps({
                "repository": "example/two-homes", "commit": commit, "run_id": 99, "attempt": 1,
                "claims": {
                    "rem:supplied": {
                        "expected": "Statements.R2", "declaration": "Proofs.R2.main",
                        "toolchain": "leanprover/lean4:v4.24.0", "axioms": [],
                        "audit_sha256": r2_audit["sha256"],
                        "statement_sha256": r2_json["statement"]["sha256"],
                        "hypotheses": "True",
                    }
                },
            }), encoding="utf-8")

            with redirect_stdout(io.StringIO()):
                atlas.build(root, ci_receipt=ci_path, commit=commit)

            # 1. dist/supplement.md generated with both supplied claims and exact details.
            supp_path = root / "dist/supplement.md"
            self.assertTrue(supp_path.is_file())
            supp_md = supp_path.read_text(encoding="utf-8")
            self.assertIn("# Supplied Proofs Supplement — Two Homes Study", supp_md)
            self.assertIn("Two Homes Provenance Note", supp_md)
            self.assertIn("Remark 2 — Positivity remark (`rem:supplied`)", supp_md)
            self.assertIn("Lean checked (proof supplied outside manuscript)", supp_md)
            self.assertIn("**Step 1.** Unfold the remark's implicit positivity assumption.", supp_md)
            self.assertIn("55 checked Lean LoC, 2 reachable local defs, 1 reachable local theorems", supp_md)
            self.assertIn("## Proposition 3 (`prop:supplied_cond`)", supp_md)
            self.assertIn("1. Assume Lemma 4.", supp_md)
            self.assertNotIn("thm:paper", supp_md)
            self.assertNotIn("lem:lean_route", supp_md)

            # 2. Dashboard, homepage, explorer, and review pages badge supplied proofs clearly.
            progress = (root / "dist/progress.html").read_text(encoding="utf-8")
            self.assertIn("Lean checked (proof supplied outside manuscript)", progress)
            self.assertIn("Conditional (assumes Lemma 4) · proof supplied outside manuscript", progress)
            self.assertIn('href="supplement.md"', progress)
            self.assertIn("<th>Supplied proof</th>", progress)
            self.assertIn("Distilled", progress)
            self.assertIn("Exploratory proof (undistilled)", progress)
            self.assertIn("55 LoC", progress)

            home = (root / "dist/index.html").read_text(encoding="utf-8")
            self.assertIn("Proof supplied outside manuscript", home)
            self.assertIn("Lean checked (proof supplied outside manuscript)", home)

            review_r2 = (root / "dist" / review.review_url("rem:supplied")).read_text(encoding="utf-8")
            self.assertIn("Lean checked (proof supplied outside manuscript)", review_r2)
            self.assertIn("Proof supplied outside manuscript", review_r2)
            self.assertIn("supplement.md#rem-supplied", review_r2)
            self.assertIn("55 checked Lean LoC", review_r2)
            self.assertIn("Distilled", review_r2)

            review_queue = (root / "dist/review.html").read_text(encoding="utf-8")
            self.assertIn("Proof supplied outside manuscript", review_queue)

            # 3. Manifest reflects supplied_proof counts, supplement.md, and proof size metrics.
            man = atlas.manifest(root, ci_receipt=ci_path, commit=commit)
            self.assertEqual(man["summary"]["supporting"]["supplied_proof"], 1)
            self.assertEqual(man["summary"]["all_results"]["supplied_proof"], 1)
            self.assertEqual(man["supplement_path"], str(supp_path))
            self.assertEqual(man["supplement"], supp_md)
            self.assertIn("Lean-supplied proof", man["markdown"])
            self.assertIn("## Supplied Proofs (Outside Manuscript)", man["markdown"])
            self.assertIn("[`supplement.md`](supplement.md)", man["markdown"])
            self.assertIn("## Proof Size & Distillation Metrics", man["markdown"])
            self.assertIn("| Remark 2 (`rem:supplied`) | 55 | 2 | 1 | Distilled |", man["markdown"])
            self.assertIn("| Lemma 5 (`lem:lean_route`) | 80 | 4 | 3 | Exploratory (undistilled) |", man["markdown"])
            self.assertIn("1 with Lean-supplied proofs", man["latex"])
            self.assertIn("supplement.md", man["latex"])

            # 4. Invalid basis is rejected cleanly.
            bad_proj = json.loads((root / "project.json").read_text(encoding="utf-8"))
            bad_proj["work"]["thm:paper"]["basis"] = "invented"
            (root / "project.json").write_text(json.dumps(bad_proj), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "basis must be one of aligned, lean, paper, supplied"):
                atlas.build(root)

            # 5. Removing all supplied claims removes stale dist/supplement.md.
            clean_reader = json.loads((root / "reader.json").read_text(encoding="utf-8"))
            clean_reader["claims"]["rem:supplied"]["basis"] = "paper"
            (root / "reader.json").write_text(json.dumps(clean_reader), encoding="utf-8")
            project["work"]["prop:supplied_cond"]["basis"] = "paper"
            (root / "project.json").write_text(json.dumps(project), encoding="utf-8")
            with redirect_stdout(io.StringIO()):
                atlas.build(root)
            self.assertFalse(supp_path.exists())

    def test_distillation_upgrade_preserves_approval_and_clears_p5_backlog(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder).resolve()
            tex = self._write_source(root, "paper.tex", r"\begin{theorem}\label{t}Distilled theorem.\end{theorem}")
            pdf = self._write_source(root, "paper.pdf", b"%PDF-1.4\n")
            stmt = self._write_source(root, "lean/Statements/T.lean", "def T : Prop := True\n")
            prf = self._write_source(root, "lean/Proofs/T.lean", "theorem main : T := trivial\n")
            self._write_source(root, "run.log", "OK\n")

            stmt_obj = self._make_stmt("Statements.T", 1, file="Statements/T.lean")
            audit_raw = {
                "expected": "Statements.T", "declaration": "Proofs.T.main",
                "axioms": [], "axiom_profile": "Constructive (0 axioms)",
                "toolchain": "leanprover/lean4:v4.24.0", "statements": ["Statements"],
                "checked_inputs": {"Statements/T.lean": stmt["sha256"], "Proofs/T.lean": prf["sha256"]},
                "statement": stmt_obj,
                "hypotheses": {"declaration": "Examples.t_wit", "proposition": "True", "axioms": []},
                "defaults": [],
                "checked_lean_loc": 420,
                "reachable_local_defs": 9,
                "reachable_local_theorems": 14,
            }
            self._write_source(root, "evidence/t.json", json.dumps(audit_raw))
            project = {
                "schema_version": 1, "environments": ["theorem"], "edition": "v1",
                "title": "Distillation Paper", "tex": [tex], "pdf": pdf,
                "proof_work": {"mode": "paper", "profile": "quick"},
                "hosting": {"decision": "local"},
                "work": {
                    "t": {
                        "status": "closed", "scope": "Matches theorem.", "run_log": "run.log",
                        "checked_inputs": {"lean/Statements/T.lean": stmt["sha256"], "lean/Proofs/T.lean": prf["sha256"]},
                        "closure": {"package": "lean", "expected": "Statements.T", "declaration": "Proofs.T.main",
                                    "audit": "evidence/t.json", "correspondence": "Matches theorem."},
                    }
                },
            }
            self._write_source(root, "project.json", json.dumps(project))

            pkt = review.get_packet(root, "t")
            review.save_comparison(root, "t", {
                "bindings": pkt["view"]["bindings"], "result": "match",
                "paper_reading": "T holds.", "lean_reading": "Statements.T holds.",
                "paper_refs": "paper.tex, t", "lean_refs": "Statements.T",
                "analysis": {
                    "summary": "Matches.", "scope": "Full theorem.",
                    "cases": [{"case": "C1", "paper": "T", "lean": "Statements.T", "why": "Direct.", "kind": "agrees"}],
                    "advice": "Approve.",
                },
            })
            pkt = review.get_packet(root, "t")
            review.decide(root, "t", pkt["token"], "approve", "Alice Author")
            self.assertTrue(review.get_packet(root, "t")["approved"])

            # Before distillation: quick-mode closure is in P5 backlog as undistilled.
            rw_before = atlas.review_work(root)
            p5_before = next(g for g in rw_before["refinement_backlog"]["priorities"] if g["priority"] == 5)
            self.assertEqual([i["claim"] for i in p5_before["items"]], ["t"])
            self.assertTrue(p5_before["items"][0]["undistilled"])

            # Distill Proofs/T.lean (without changing Statements/T.lean), re-audit with lower LoC, mark distilled: True.
            prf2 = self._write_source(root, "lean/Proofs/T.lean", "-- distilled\ntheorem main : T := trivial\n")
            audit_raw["checked_inputs"]["Proofs/T.lean"] = prf2["sha256"]
            audit_raw["checked_lean_loc"] = 45
            audit_raw["reachable_local_defs"] = 2
            audit_raw["reachable_local_theorems"] = 1
            self._write_source(root, "evidence/t.json", json.dumps(audit_raw))
            project["work"]["t"]["checked_inputs"]["lean/Proofs/T.lean"] = prf2["sha256"]
            project["work"]["t"]["distilled"] = True
            self._write_source(root, "project.json", json.dumps(project))

            with redirect_stdout(io.StringIO()):
                atlas.build(root)

            # Approval carries over automatically because Statements/T.lean (statement.sha256) is unchanged!
            self.assertTrue(review.get_packet(root, "t")["approved"])
            rw_after = atlas.review_work(root)
            self.assertEqual(rw_after["refinement_backlog"]["total_items"], 0)
            progress = (root / "dist/progress.html").read_text(encoding="utf-8")
            self.assertIn("Distilled", progress)
            self.assertIn("45 LoC", progress)
            self.assertNotIn("Exploratory proof (undistilled)", progress)


if __name__ == "__main__":
    unittest.main()
