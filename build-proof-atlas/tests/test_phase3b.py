"""Phase 3b unit and Lean 4.33.1 integration tests: opt-in 1:1 step_map + compiled-Expr auditUses."""
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import atlas
import audit_lean
import author_review as review
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


class Phase3bUnitTests(unittest.TestCase):
    def test_normalize_step_map_validation_and_digest_stability(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            sm_path = root / "steps.json"
            raw = {
                "steps": [
                    {"id": "s1", "lemma": "Proofs.B.step_1", "step_deps": [], "origin": "paper", "tex": "First step.", "text": "Prose 1"},
                    {"id": "s2", "lemma": "Proofs.B.step_2", "step_deps": ["Proofs.B.step_1"], "origin": "supplied", "text": "Prose 2"},
                ],
                "main_deps": ["s2"],
            }
            sm_path.write_text(json.dumps(raw), encoding="utf-8")

            norm_from_file = audit_lean.normalize_step_map(sm_path, declaration="Proofs.B.main", root=root)
            self.assertEqual(norm_from_file["main_declaration"], "Proofs.B.main")
            self.assertEqual(norm_from_file["main_deps"], ["s2"])
            self.assertEqual(norm_from_file["steps"][1]["step_deps"], ["s1"])

            # Editing prose/tex leaves Lean step_map_sha256 unchanged; editing step_deps changes it.
            raw_edited_prose = json.loads(json.dumps(raw))
            raw_edited_prose["steps"][0]["text"] = "Updated English explanation"
            norm_prose = audit_lean.normalize_step_map(raw_edited_prose, declaration="Proofs.B.main")
            self.assertEqual(norm_prose["step_map_sha256"], norm_from_file["step_map_sha256"])

            raw_edited_deps = json.loads(json.dumps(raw))
            raw_edited_deps["steps"][1]["step_deps"] = []
            norm_deps = audit_lean.normalize_step_map(raw_edited_deps, declaration="Proofs.B.main")
            self.assertNotEqual(norm_deps["step_map_sha256"], norm_from_file["step_map_sha256"])

            # Bare list shorthand is also accepted.
            norm_list = audit_lean.normalize_step_map(raw["steps"], declaration="Proofs.B.main")
            self.assertIsNone(norm_list["main_deps"])
            self.assertEqual(len(norm_list["steps"]), 2)

            # Invalid cases rejected cleanly.
            with self.assertRaisesRegex(ValueError, "non-empty 'steps' list"):
                audit_lean.normalize_step_map({"steps": []}, declaration="Proofs.B.main")
            with self.assertRaisesRegex(ValueError, "Duplicate step id"):
                audit_lean.normalize_step_map([
                    {"id": "s1", "lemma": "Proofs.B.a"},
                    {"id": "s1", "lemma": "Proofs.B.b"},
                ], declaration="Proofs.B.main")
            with self.assertRaisesRegex(ValueError, "Duplicate Lean lemma"):
                audit_lean.normalize_step_map([
                    {"id": "s1", "lemma": "Proofs.B.a"},
                    {"id": "s2", "lemma": "Proofs.B.a"},
                ], declaration="Proofs.B.main")
            with self.assertRaisesRegex(ValueError, "cannot be the claim's main declaration"):
                audit_lean.normalize_step_map([
                    {"id": "s1", "lemma": "Proofs.B.main"},
                ], declaration="Proofs.B.main")
            with self.assertRaisesRegex(ValueError, "origin must be 'paper' or 'supplied'"):
                audit_lean.normalize_step_map([
                    {"id": "s1", "lemma": "Proofs.B.a", "origin": "guess"},
                ], declaration="Proofs.B.main")
            with self.assertRaisesRegex(ValueError, "cannot depend on itself"):
                audit_lean.normalize_step_map([
                    {"id": "s1", "lemma": "Proofs.B.a", "step_deps": ["s1"]},
                ], declaration="Proofs.B.main")
            with self.assertRaisesRegex(ValueError, "unknown step"):
                audit_lean.normalize_step_map([
                    {"id": "s1", "lemma": "Proofs.B.a", "step_deps": ["s99"]},
                ], declaration="Proofs.B.main")
            with self.assertRaisesRegex(ValueError, "Cyclic step_deps"):
                audit_lean.normalize_step_map([
                    {"id": "s1", "lemma": "Proofs.B.a", "step_deps": ["s2"]},
                    {"id": "s2", "lemma": "Proofs.B.b", "step_deps": ["s1"]},
                ], declaration="Proofs.B.main")

            # --statement-only rejects --step-map.
            (root / "Contract.lean").write_text("-- stub\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "--statement-only does not accept --step-map"):
                audit_lean.audit(SimpleNamespace(
                    package=root, contract="Contract.lean", expected="Statements.Main",
                    statements=["Statements"], step_map=sm_path, statement_only=True,
                ))

    def test_parse_step_audit_invariants(self):
        sm = audit_lean.normalize_step_map({
            "steps": [
                {"id": "s1", "lemma": "Proofs.B.step_1", "step_deps": [], "origin": "paper"},
                {"id": "s2", "lemma": "Proofs.B.step_2", "step_deps": ["s1"], "origin": "supplied"},
                {"id": "s3", "lemma": "Proofs.B.step_3", "step_deps": ["s2"], "origin": "paper"},
            ],
            "main_deps": ["s3"],
        }, declaration="Proofs.B.main")

        def make_output(step_overrides=None, main_override=None):
            steps = {
                "Proofs.B.step_1": {
                    "lemma": "Proofs.B.step_1", "theorem_info": True, "module": "Proofs.B",
                    "lines": [4, 6], "axioms": [], "used_steps": [],
                    "used_statements": ["LemA.Statement"], "forbidden_mains": [],
                },
                "Proofs.B.step_2": {
                    "lemma": "Proofs.B.step_2", "theorem_info": True, "module": "Proofs.B",
                    "lines": [8, 12], "axioms": ["propext"], "used_steps": ["Proofs.B.step_1"],
                    "used_statements": [], "forbidden_mains": [],
                },
                "Proofs.B.step_3": {
                    "lemma": "Proofs.B.step_3", "theorem_info": True, "module": "Proofs.B",
                    "lines": [14, 16], "axioms": [], "used_steps": ["Proofs.B.step_2"],
                    "used_statements": [], "forbidden_mains": [],
                },
            }
            for k, v in (step_overrides or {}).items():
                steps[k].update(v)
            main_row = {
                "declaration": "Proofs.B.main", "main_declaration": "Proofs.B.main",
                "theorem_info": True, "decl_uses_main": True, "module": "Proofs.B",
                "axioms": ["propext"], "used_steps": ["Proofs.B.step_3"],
                "used_statements": ["LemA.Statement"], "forbidden_mains": [],
            }
            main_row.update(main_override or {})
            lines = ["PROOF-ATLAS-STEP-AUDIT " + json.dumps(r) for r in steps.values()]
            lines.append("PROOF-ATLAS-MAIN-AUDIT " + json.dumps(main_row))
            return "\n".join(lines) + "\n"

        parsed = audit_lean.parse_step_audit(
            make_output(), sm, "Proofs.B.main", local_modules={"Proofs.B": "Proofs/B.lean"},
        )
        self.assertTrue(parsed["verified"])
        self.assertEqual(parsed["main_steps"], ["s3"])
        self.assertEqual(parsed["step_count"], 3)
        self.assertEqual(parsed["steps"][0]["file"], "Proofs/B.lean")
        self.assertEqual(parsed["steps"][0]["used_statements"], ["LemA.Statement"])
        self.assertEqual(parsed["steps"][2]["used_deps"], ["s2"])

        # Undeclared step dependency rejected.
        with self.assertRaisesRegex(ValueError, r"uses undeclared step lemma\(s\): s1"):
            audit_lean.parse_step_audit(
                make_output({"Proofs.B.step_3": {"used_steps": ["Proofs.B.step_1", "Proofs.B.step_2"]}}),
                sm, "Proofs.B.main",
            )
        # Unused declared step dependency rejected.
        with self.assertRaisesRegex(ValueError, r"declares unused step dependency\(ies\): s1"):
            audit_lean.parse_step_audit(
                make_output({"Proofs.B.step_2": {"used_steps": []}}),
                sm, "Proofs.B.main",
            )
        # Forbidden main call from step rejected.
        with self.assertRaisesRegex(ValueError, r"directly calls another claim's main theorem\(s\): Proofs\.A\.main"):
            audit_lean.parse_step_audit(
                make_output({"Proofs.B.step_1": {"forbidden_mains": ["Proofs.A.main"]}}),
                sm, "Proofs.B.main",
            )
        # Forbidden main call from main rejected.
        with self.assertRaisesRegex(ValueError, r"Main declaration Proofs\.B\.main directly calls another claim's main theorem\(s\): Proofs\.A\.main"):
            audit_lean.parse_step_audit(
                make_output(main_override={"forbidden_mains": ["Proofs.A.main"]}),
                sm, "Proofs.B.main",
            )
        # Non-theorem step lemma rejected.
        with self.assertRaisesRegex(ValueError, r"must be a Lean theorem \(\.thmInfo\)"):
            audit_lean.parse_step_audit(
                make_output({"Proofs.B.step_1": {"theorem_info": False}}),
                sm, "Proofs.B.main",
            )
        # Extra axiom (sorryAx) in step lemma rejected.
        with self.assertRaisesRegex(ValueError, "uses additional axioms: sorryAx"):
            audit_lean.parse_step_audit(
                make_output({"Proofs.B.step_2": {"axioms": ["sorryAx"]}}),
                sm, "Proofs.B.main",
            )
        # Wrapper declaration that does not use main_declaration rejected.
        with self.assertRaisesRegex(ValueError, "does not use step-mapped main declaration"):
            audit_lean.parse_step_audit(
                make_output(main_override={"decl_uses_main": False}),
                sm, "Assembly.thm_b",
            )
        # Main deps mismatch rejected.
        with self.assertRaisesRegex(ValueError, "declares unused main_deps: s3"):
            audit_lean.parse_step_audit(
                make_output(main_override={"used_steps": ["Proofs.B.step_2"]}),
                sm, "Proofs.B.main",
            )
        # Orphan step rejected when main_deps is omitted.
        sm_orphan = audit_lean.normalize_step_map({
            "steps": [
                {"id": "s1", "lemma": "Proofs.B.step_1", "step_deps": []},
                {"id": "s2", "lemma": "Proofs.B.step_2", "step_deps": []},
                {"id": "s3", "lemma": "Proofs.B.step_3", "step_deps": ["s2"]},
            ],
        }, declaration="Proofs.B.main")
        with self.assertRaisesRegex(ValueError, "not used in the proof of Proofs.B.main: s1"):
            audit_lean.parse_step_audit(
                make_output({"Proofs.B.step_2": {"used_steps": []}}),
                sm_orphan, "Proofs.B.main",
            )

    def test_verbatim_tex_provenance_badges_supplement_manifest_and_explorer(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            tex = _write_source(root, "paper.tex", (
                r"\begin{theorem}[Paper Steps Theorem]\label{thm:paper}" "\n"
                r"Every positive number satisfies the bound." "\n"
                r"\end{theorem}" "\n"
                r"\begin{proof}" "\n"
                r"First, rewrite the left-hand side via identity (1)." "\n"
                r"Second, apply monotonicity to conclude the inequality." "\n"
                r"\end{proof}" "\n"
                r"\begin{theorem}[Mixed Steps Theorem]\label{thm:mixed}" "\n"
                r"The shifted sequence remains nonnegative." "\n"
                r"\end{theorem}" "\n"
                r"\begin{proof}" "\n"
                r"Observe that the base term is nonnegative." "\n"
                r"The remaining inductive step follows immediately." "\n"
                r"\end{proof}" "\n"
                r"\begin{lemma}[Draft Step Lemma]\label{lem:draft}" "\n"
                r"Auxiliary estimate." "\n"
                r"\end{lemma}" "\n"
                r"\begin{proof}By direct substitution.\end{proof}" "\n"
            ))
            pdf = _write_source(root, "paper.pdf", b"%PDF-1.4\n")
            stmt = _write_source(root, "lean/Statements/All.lean", (
                "def PaperStmt : Prop := True\n"
                "def MixedStmt : Prop := True\n"
                "def DraftStmt : Prop := True\n"
            ))
            prf1 = _write_source(root, "lean/Proofs/Paper.lean", "theorem main : PaperStmt := trivial\n")
            prf2 = _write_source(root, "lean/Proofs/Mixed.lean", "theorem main : MixedStmt := trivial\n")
            _write_source(root, "run.log", "OK\n")

            sm_paper_raw = {
                "steps": [
                    {
                        "id": "s1", "lemma": "Proofs.Paper.step_1", "step_deps": [],
                        "origin": "paper", "title": "Identity rewrite",
                        "tex": "First, rewrite the left-hand side via identity (1).",
                        "text": "Rewrite the LHS using identity (1).",
                    },
                    {
                        "id": "s2", "lemma": "Proofs.Paper.step_2", "step_deps": ["s1"],
                        "origin": "paper", "title": "Monotonicity conclusion",
                        "tex": "Second, apply monotonicity to conclude the inequality.",
                        "text": "Apply monotonicity to s1.",
                    },
                ],
                "main_deps": ["s2"],
            }
            sm_mixed_raw = {
                "steps": [
                    {
                        "id": "s1", "lemma": "Proofs.Mixed.step_1", "step_deps": [],
                        "origin": "paper", "title": "Base term",
                        "tex": "Observe that the base term is nonnegative.",
                        "text": "Establish the nonnegative base case.",
                    },
                    {
                        "id": "s2", "lemma": "Proofs.Mixed.step_2", "step_deps": ["s1"],
                        "origin": "supplied", "title": "Implicit regularity glue",
                        "text": "Supply the omitted measurability and induction bridge in Lean.",
                    },
                ],
                "main_deps": ["s2"],
            }
            sm_draft_raw = {
                "steps": [
                    {
                        "id": "s1", "lemma": "Proofs.Draft.step_1", "step_deps": [],
                        "origin": "paper",
                        "tex": "By direct substitution.",
                    },
                ],
            }
            _write_source(root, "steps/paper.json", json.dumps(sm_paper_raw, indent=2))
            _write_source(root, "steps/mixed.json", json.dumps(sm_mixed_raw, indent=2))

            norm_paper = audit_lean.normalize_step_map(sm_paper_raw, declaration="Proofs.Paper.main")
            norm_mixed = audit_lean.normalize_step_map(sm_mixed_raw, declaration="Proofs.Mixed.main")

            def make_audit(expected, decl, prf_info, norm_sm, line):
                sha = hashlib.sha256(expected.encode()).hexdigest()
                return {
                    "expected": expected, "declaration": decl, "axioms": [],
                    "axiom_profile": "Constructive (0 axioms)",
                    "toolchain": "leanprover/lean4:v4.33.1", "statements": ["Statements"],
                    "theorem_info": True,
                    "checked_inputs": {
                        "Statements/All.lean": stmt["sha256"],
                        prf_info["path"].removeprefix("lean/"): prf_info["sha256"],
                    },
                    "statement": {
                        "expected": expected,
                        "sha256": hashlib.sha256(f"{expected} {sha}\n".encode()).hexdigest(),
                        "constants": [{"name": expected, "file": "Statements/All.lean", "lines": [line, line], "sha256": sha}],
                    },
                    "hypotheses": {"declaration": "Examples.wit", "proposition": "True", "axioms": []},
                    "defaults": [],
                    "step_audit": {
                        "verified": True,
                        "declaration": decl,
                        "main_declaration": decl,
                        "main_steps": ["s2"],
                        "main_statements": [],
                        "forbidden_mains_checked": True,
                        "step_count": 2,
                        "step_map_sha256": norm_sm["step_map_sha256"],
                        "steps": [
                            {
                                "id": s["id"], "lemma": s["lemma"], "module": prf_info["path"].removeprefix("lean/")[:-5].replace("/", "."),
                                "file": prf_info["path"].removeprefix("lean/"), "lines": [1, 1],
                                "theorem_info": True, "axioms": [],
                                "declared_deps": list(s["step_deps"]), "used_deps": list(s["step_deps"]),
                                "used_statements": [], "origin": s["origin"],
                            }
                            for s in norm_sm["steps"]
                        ],
                    },
                }

            _write_source(root, "evidence/paper.json", json.dumps(make_audit("PaperStmt", "Proofs.Paper.main", prf1, norm_paper, 1)))
            _write_source(root, "evidence/mixed.json", json.dumps(make_audit("MixedStmt", "Proofs.Mixed.main", prf2, norm_mixed, 2)))

            reader = {
                "schema_version": 1,
                "claims": {
                    "thm:paper": {"reference": "Theorem 1", "basis": "aligned", "step_map": "steps/paper.json"},
                    "thm:mixed": {"reference": "Theorem 2", "basis": "paper"},
                    "lem:draft": {"reference": "Lemma 3", "step_map": sm_draft_raw},
                },
                "dependencies": [],
            }
            _write_source(root, "reader.json", json.dumps(reader))

            project = {
                "schema_version": 1, "environments": ["theorem", "lemma"],
                "edition": "v1", "title": "Step Verification Atlas",
                "authors": ["Ada Analyst"], "tex": [tex], "pdf": pdf, "reader": "reader.json",
                "proof_work": {"mode": "paper", "profile": "thorough"},
                "hosting": {"decision": "local"},
                "work": {
                    "thm:paper": {
                        "status": "closed", "scope": "Matches Theorem 1.", "run_log": "run.log",
                        "checked_inputs": {"lean/Statements/All.lean": stmt["sha256"], prf1["path"]: prf1["sha256"]},
                        "closure": {"package": "lean", "expected": "PaperStmt", "declaration": "Proofs.Paper.main",
                                    "audit": "evidence/paper.json", "correspondence": "Matches Theorem 1."},
                    },
                    "thm:mixed": {
                        "status": "closed", "scope": "Matches Theorem 2.", "run_log": "run.log",
                        "step_map": "steps/mixed.json",
                        "checked_inputs": {"lean/Statements/All.lean": stmt["sha256"], prf2["path"]: prf2["sha256"]},
                        "closure": {"package": "lean", "expected": "MixedStmt", "declaration": "Proofs.Mixed.main",
                                    "audit": "evidence/mixed.json", "correspondence": "Matches Theorem 2."},
                    },
                    "lem:draft": {"status": "drafted", "scope": "In progress."},
                },
            }
            _write_source(root, "project.json", json.dumps(project))

            with redirect_stdout(io.StringIO()):
                atlas.build(root)

            # 1. Dashboard, homepage, review pages, and explorer payload reflect exact step badges.
            progress = (root / "dist/progress.html").read_text(encoding="utf-8")
            self.assertIn("Step-verified (paper)", progress)
            self.assertIn("Step-verified (with supplied steps)", progress)
            self.assertIn("supplement.md#thm-mixed", progress)

            home = (root / "dist/index.html").read_text(encoding="utf-8")
            self.assertIn("Step-verified (paper)", home)
            self.assertIn("Step-verified (with supplied steps)", home)

            rev_paper = (root / "dist" / review.review_url("thm:paper")).read_text(encoding="utf-8")
            self.assertIn("Step-verified (paper)", rev_paper)
            rev_mixed = (root / "dist" / review.review_url("thm:mixed")).read_text(encoding="utf-8")
            self.assertIn("Step-verified (with supplied steps)", rev_mixed)
            self.assertIn("supplement.md#thm-mixed", rev_mixed)

            html = (root / "dist/proofs/index.html").read_text(encoding="utf-8")
            marker = '<script id="atlas-data" type="application/json">'
            start = html.index(marker) + len(marker)
            end = html.index("</script>", start)
            payload = json.loads(html[start:end].replace(r"\u003c", "<"))
            by_cid = {c["id"]: c for c in payload["claims"]}

            self.assertEqual(by_cid["thm:paper"]["verification"]["step_badge"], "Step-verified (paper)")
            self.assertTrue(by_cid["thm:paper"]["step_verification"]["steps"][0]["tex_verified"])
            self.assertEqual(by_cid["thm:paper"]["step_verification"]["steps"][0]["tex_file"], "paper.tex")
            self.assertEqual(by_cid["thm:paper"]["step_verification"]["steps"][0]["tex_line"], 5)

            self.assertEqual(by_cid["thm:mixed"]["verification"]["step_badge"], "Step-verified (with supplied steps)")
            self.assertEqual(by_cid["thm:mixed"]["verification"]["supplied_step_count"], 1)
            self.assertFalse(by_cid["thm:mixed"]["step_verification"]["steps"][1]["tex_verified"])

            # Draft claim has structured steps for preview but NO verified badge!
            self.assertFalse(by_cid["lem:draft"]["step_verification"]["verified"])
            self.assertNotIn("step_verified", by_cid["lem:draft"]["verification"])

            # explorer.js supports structured Lamport steps and 1:1 Step-Lemma Expr Audit.
            explorer_js = (root / "dist/explorer.js").read_text(encoding="utf-8")
            self.assertIn("Structured Lamport steps", explorer_js)
            self.assertIn("1:1 Step-Lemma Expr Audit", explorer_js)
            self.assertIn("verbatim TeX verified", explorer_js)

            # 2. dist/supplement.md includes thm:mixed's supplied step and excludes thm:paper!
            supp_md = (root / "dist/supplement.md").read_text(encoding="utf-8")
            self.assertIn("Theorem 2 — Mixed Steps Theorem (`thm:mixed`)", supp_md)
            self.assertIn("Step-verified (with supplied steps)", supp_md)
            self.assertIn("### Supplied Proof Steps (Outside Manuscript)", supp_md)
            self.assertIn("Proofs.Mixed.step_2", supp_md)
            self.assertIn("Supply the omitted measurability and induction bridge in Lean.", supp_md)
            self.assertNotIn("thm:paper", supp_md)

            # 3. dist/VERIFICATION.md and LaTeX snippet include step verification section & counts.
            man = atlas.manifest(root)
            self.assertEqual(man["summary"]["headline"]["step_verified_paper"], 1)
            self.assertEqual(man["summary"]["headline"]["step_verified_with_supplied"], 1)
            self.assertIn("## Step-Level Verification (1:1 Expr Audit)", man["markdown"])
            self.assertIn("Step-verified (paper)", man["markdown"])
            self.assertIn("Step-verified (with supplied steps)", man["markdown"])
            self.assertIn("2 (2 paper / 0 supplied)", man["markdown"])
            self.assertIn("2 (1 paper / 1 supplied)", man["markdown"])
            self.assertIn("Step-verified (paper)", man["latex"])
            self.assertIn("Step-verified (with supplied steps)", man["latex"])

            # 4. Negative provenance checks: tampered verbatim TeX substring fails loudly.
            bad_paper = json.loads(json.dumps(sm_paper_raw))
            bad_paper["steps"][0]["tex"] = "First, rewrite the left-hand side via identity (2)."
            _write_source(root, "steps/paper.json", json.dumps(bad_paper))
            with self.assertRaisesRegex(ValueError, "not a verbatim substring of the bound TeX sources"):
                atlas.build(root)

            # Missing origin fails loudly.
            bad_origin = json.loads(json.dumps(sm_paper_raw))
            del bad_origin["steps"][0]["origin"]
            _write_source(root, "steps/paper.json", json.dumps(bad_origin))
            with self.assertRaisesRegex(ValueError, "must declare origin 'paper' or 'supplied'"):
                atlas.build(root)

            # Stale step_map_sha256 relative to receipt fails loudly.
            stale_paper = json.loads(json.dumps(sm_paper_raw))
            stale_paper["steps"][1]["step_deps"] = []
            _write_source(root, "steps/paper.json", json.dumps(stale_paper))
            with self.assertRaisesRegex(ValueError, "step_map changed since the recorded Lean step audit"):
                atlas.build(root)

            # Missing step_map on a claim whose receipt has paper step_audit fails loudly.
            _write_source(root, "steps/paper.json", json.dumps(sm_paper_raw))
            reader_no_sm = json.loads(json.dumps(reader))
            del reader_no_sm["claims"]["thm:paper"]["step_map"]
            _write_source(root, "reader.json", json.dumps(reader_no_sm))
            with self.assertRaisesRegex(ValueError, "no step_map is configured"):
                atlas.build(root)


@unittest.skipUnless(os.environ.get("ELAN_TOOLCHAIN"), "requires an installed pinned Lean toolchain")
class Phase3bLeanIntegration(unittest.TestCase):
    def test_live_lean_audit_uses_auxiliaries_stopping_and_forbidden_mains(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            pin = os.environ["ELAN_TOOLCHAIN"]
            (root / "lean-toolchain").write_text(pin + "\n", encoding="utf-8")
            (root / "lakefile.toml").write_text(
                'name = "Phase3bStepAudit"\n'
                '[[lean_lib]]\nname = "Prelude"\n'
                '[[lean_lib]]\nname = "Statements"\n'
                '[[lean_lib]]\nname = "Routine"\n'
                '[[lean_lib]]\nname = "Proofs"\n',
                encoding="utf-8",
            )
            sources = {
                "Prelude.lean": "-- pure external imports only\n",
                "Statements/Main.lean": (
                    "import Prelude\n"
                    "namespace LemA\n"
                    "def Statement : Prop := ∀ n : Nat, n + 0 = n\n"
                    "end LemA\n"
                    "namespace ThmB\n"
                    "def Statement : Prop := ∀ n : Nat, (n + 0) + 1 = n + 1\n"
                    "end ThmB\n"
                ),
                "Routine/Glue.lean": (
                    "import Prelude\n"
                    "theorem succ_eq_of_eq {a b : Nat} (h : a = b) : a + 1 = b + 1 := congrArg (· + 1) h\n"
                ),
                "Proofs/A.lean": (
                    "import Statements.Main\n"
                    "namespace ProofsA\n"
                    "theorem main : LemA.Statement := Nat.add_zero\n"
                    "theorem other_entry : LemA.Statement := Nat.add_zero\n"
                    "end ProofsA\n"
                ),
                "Proofs/B.lean": (
                    "import Statements.Main\n"
                    "import Routine.Glue\n"
                    "import Proofs.A\n"
                    "namespace ProofsB\n"
                    "theorem step_1 (hA : LemA.Statement) (n : Nat) : n + 0 = n := hA n\n"
                    "private theorem local_wrap (hA : LemA.Statement) (n : Nat) : n + 0 = n := step_1 hA n\n"
                    "-- Uses `match` + `by omega` so Lean generates compiler auxiliaries (match_1 / _proof_1)\n"
                    "-- while invoking `step_1` through `local_wrap` and a match branch.\n"
                    "theorem step_2 (hA : LemA.Statement) (n : Nat) : (n + 0) + 1 = n + 1 := by\n"
                    "  match n with\n"
                    "  | 0 =>\n"
                    "    have h0 := step_1 hA 0\n"
                    "    omega\n"
                    "  | k + 1 =>\n"
                    "    have hk := local_wrap hA (k + 1)\n"
                    "    exact succ_eq_of_eq hk\n"
                    "-- Calls only `step_2` (NOT `step_1` directly): tests stopping at sibling step lemma `step_2`.\n"
                    "theorem step_3 (hA : LemA.Statement) (n : Nat) : (n + 0) + 1 = n + 1 := step_2 hA n\n"
                    "theorem main (hA : LemA.Statement) : ThmB.Statement := fun n => step_3 hA n\n"
                    "-- Negative fixtures:\n"
                    "theorem step_orphan (n : Nat) : n = n := rfl\n"
                    "theorem step_calls_other_main (n : Nat) : n + 0 = n := ProofsA.main n\n"
                    "private theorem smuggle_other_main (n : Nat) : n + 0 = n := ProofsA.main n\n"
                    "theorem step_smuggles_main (n : Nat) : n + 0 = n := smuggle_other_main n\n"
                    "theorem step_calls_other_entry (n : Nat) : n + 0 = n := ProofsA.other_entry n\n"
                    "theorem main_calls_other_main : ThmB.Statement := fun n => succ_eq_of_eq (ProofsA.main n)\n"
                    "theorem main_via_bad_step : ThmB.Statement := fun n => succ_eq_of_eq (step_calls_other_main n)\n"
                    "theorem main_via_smuggle : ThmB.Statement := fun n => succ_eq_of_eq (step_smuggles_main n)\n"
                    "theorem main_via_other_entry : ThmB.Statement := fun n => succ_eq_of_eq (step_calls_other_entry n)\n"
                    "def def_not_thm (n : Nat) : n = n := rfl\n"
                    "theorem main_via_def (hA : LemA.Statement) : ThmB.Statement := by\n"
                    "  have _ := def_not_thm 0\n"
                    "  exact fun n => step_3 hA n\n"
                    "end ProofsB\n"
                ),
                "ContractB.lean": "import Statements.Main\nimport Proofs.B\n",
            }
            for rel, body in sources.items():
                _write_source(root, rel, body)

            env = os.environ.copy()
            lake = audit_lean.select_lake(root, pin, env, sys.stderr, offline=True)
            subprocess.run([*lake, "update"], cwd=root, env=env, check=True)

            valid_sm = {
                "steps": [
                    {"id": "s1", "lemma": "ProofsB.step_1", "step_deps": [], "origin": "paper"},
                    {"id": "s2", "lemma": "ProofsB.step_2", "step_deps": ["s1"], "origin": "paper"},
                    {"id": "s3", "lemma": "ProofsB.step_3", "step_deps": ["s2"], "origin": "supplied"},
                ],
                "main_deps": ["s3"],
            }
            sm_file = root / "step_map.json"
            sm_file.write_text(json.dumps(valid_sm, indent=2), encoding="utf-8")

            spec = SimpleNamespace(
                package=root, contract="ContractB.lean", expected="ThmB.Statement",
                declaration="ProofsB.main", target=["Proofs.B"], statements=["Statements"],
                routine=["Routine"], assumes=["LemA.Statement"], step_map=sm_file,
            )

            # 1. Identical receipts from sequential audit() and batched audit_batch().
            seq_r = audit_lean.audit(spec)
            bat_r = audit_lean.audit_batch(root, [spec])[0]
            self.assertEqual(bat_r, seq_r)

            sa = seq_r["step_audit"]
            self.assertTrue(sa["verified"])
            self.assertEqual(sa["main_declaration"], "ProofsB.main")
            self.assertEqual(sa["main_steps"], ["s3"])
            self.assertEqual(sa["step_count"], 3)
            by_step = {s["id"]: s for s in sa["steps"]}
            self.assertEqual(by_step["s1"]["used_deps"], [])
            self.assertIn("LemA.Statement", by_step["s1"]["used_statements"])
            self.assertEqual(by_step["s2"]["used_deps"], ["s1"])
            # Stopping at sibling step_2: s3 sees ONLY s2, never leaks transitive s1!
            self.assertEqual(by_step["s3"]["used_deps"], ["s2"])
            self.assertEqual(by_step["s1"]["file"], "Proofs/B.lean")
            self.assertTrue(all(s["theorem_info"] for s in sa["steps"]))

            # 2. CLI --step-map produces the same step_audit JSON.
            cli_out = root / "cli_receipt.json"
            cli_cmd = [
                sys.executable, str(Path(__file__).resolve().parents[1] / "scripts/audit_lean.py"),
                str(root), "ContractB.lean", "ThmB.Statement", "ProofsB.main",
                "--target", "Proofs.B", "--statements", "Statements", "--routine", "Routine",
                "--assumes", "LemA.Statement", "--step-map", str(sm_file), "--output", str(cli_out),
            ]
            subprocess.run(cli_cmd, check=True, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            cli_data = json.loads(cli_out.read_text(encoding="utf-8"))
            self.assertEqual(cli_data["step_audit"], sa)

            # 3. Undeclared step_deps (hiding s1 inside match/_proof_1/local_wrap) is caught!
            missing_dep_sm = json.loads(json.dumps(valid_sm))
            missing_dep_sm["steps"][1]["step_deps"] = []
            with self.assertRaisesRegex(ValueError, r"Step 's2' \(ProofsB\.step_2\).*uses undeclared step lemma\(s\): s1"):
                audit_lean.audit(SimpleNamespace(**{**vars(spec), "step_map": missing_dep_sm}))

            # 4. Unused declared step_deps (declaring transitive s1 on s3 when s3 only calls s2) is caught!
            extra_dep_sm = json.loads(json.dumps(valid_sm))
            extra_dep_sm["steps"][2]["step_deps"] = ["s1", "s2"]
            with self.assertRaisesRegex(ValueError, r"Step 's3' \(ProofsB\.step_3\).*declares unused step dependency\(ies\): s1"):
                audit_lean.audit(SimpleNamespace(**{**vars(spec), "step_map": extra_dep_sm}))

            # 5. Direct call to another claim's `main` from a step lemma is forbidden!
            with self.assertRaisesRegex(ValueError, r"directly calls another claim's main theorem\(s\): ProofsA\.main"):
                audit_lean.audit(SimpleNamespace(
                    package=root, contract="ContractB.lean", expected="ThmB.Statement",
                    declaration="ProofsB.main_via_bad_step", target=["Proofs.B"],
                    statements=["Statements"], routine=["Routine"],
                    step_map={"steps": [{"id": "s1", "lemma": "ProofsB.step_calls_other_main", "step_deps": []}]},
                ))

            # 6. Indirect call to another claim's `main` through a private helper is ALSO caught!
            with self.assertRaisesRegex(ValueError, r"directly calls another claim's main theorem\(s\): ProofsA\.main"):
                audit_lean.audit(SimpleNamespace(
                    package=root, contract="ContractB.lean", expected="ThmB.Statement",
                    declaration="ProofsB.main_via_smuggle", target=["Proofs.B"],
                    statements=["Statements"], routine=["Routine"],
                    step_map={"steps": [{"id": "s1", "lemma": "ProofsB.step_smuggles_main", "step_deps": []}]},
                ))

            # 7. Direct call to another claim's `main` from main itself is forbidden!
            with self.assertRaisesRegex(ValueError, r"directly calls another claim's main theorem\(s\): ProofsA\.main"):
                audit_lean.audit(SimpleNamespace(
                    package=root, contract="ContractB.lean", expected="ThmB.Statement",
                    declaration="ProofsB.main_calls_other_main", target=["Proofs.B"],
                    statements=["Statements"], routine=["Routine"],
                    step_map={"steps": [{"id": "s1", "lemma": "ProofsB.step_orphan", "step_deps": []}]},
                ))

            # 8. Explicit forbidden_mains blocks non-`main`-named theorems from other claims!
            with self.assertRaisesRegex(ValueError, r"directly calls another claim's main theorem\(s\): ProofsA\.other_entry"):
                audit_lean.audit(SimpleNamespace(
                    package=root, contract="ContractB.lean", expected="ThmB.Statement",
                    declaration="ProofsB.main_via_other_entry", target=["Proofs.B"],
                    statements=["Statements"], routine=["Routine"],
                    step_map={
                        "steps": [{"id": "s1", "lemma": "ProofsB.step_calls_other_entry", "step_deps": []}],
                        "forbidden_mains": ["ProofsA.other_entry"],
                    },
                ))

            # 9. Non-theorem (`def`) step lemma is rejected!
            with self.assertRaisesRegex(ValueError, r"Step 's0' declaration ProofsB\.def_not_thm must be a Lean theorem \(\.thmInfo\)"):
                audit_lean.audit(SimpleNamespace(
                    package=root, contract="ContractB.lean", expected="ThmB.Statement",
                    declaration="ProofsB.main_via_def", target=["Proofs.B"],
                    statements=["Statements"], routine=["Routine"], assumes=["LemA.Statement"],
                    step_map={"steps": [
                        {"id": "s0", "lemma": "ProofsB.def_not_thm", "step_deps": []},
                        {"id": "s1", "lemma": "ProofsB.step_1", "step_deps": []},
                        {"id": "s2", "lemma": "ProofsB.step_2", "step_deps": ["s1"]},
                        {"id": "s3", "lemma": "ProofsB.step_3", "step_deps": ["s2"]},
                    ]},
                ))

            # 10. Orphan/unused step lemma is rejected!
            orphan_sm = {
                "steps": [
                    {"id": "s1", "lemma": "ProofsB.step_1", "step_deps": []},
                    {"id": "s2", "lemma": "ProofsB.step_2", "step_deps": ["s1"]},
                    {"id": "s3", "lemma": "ProofsB.step_3", "step_deps": ["s2"]},
                    {"id": "s_dead", "lemma": "ProofsB.step_orphan", "step_deps": []},
                ],
            }
            with self.assertRaisesRegex(ValueError, "not used in the proof of ProofsB.main: s_dead"):
                audit_lean.audit(SimpleNamespace(**{**vars(spec), "step_map": orphan_sm}))

    def test_live_lean_assemble_verify_ci_and_atlas_end_to_end(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            pin = os.environ["ELAN_TOOLCHAIN"]
            tex = _write_source(root, "paper.tex", (
                r"\begin{lemma}[Add Zero]\label{lem:a}For every $n$, $n + 0 = n$.\end{lemma}" "\n"
                r"\begin{theorem}[Shifted Identity]\label{thm:b}For every $n$, $(n + 0) + 1 = n + 1$.\end{theorem}" "\n"
                r"\begin{proof}" "\n"
                r"Apply Lemma A to reduce $n + 0$ to $n$." "\n"
                r"Add $1$ to both sides to conclude." "\n"
                r"\end{proof}" "\n"
                r"\begin{corollary}[Double Shift]\label{cor:c}For every $n$, $((n + 0) + 1) + 0 = n + 1$.\end{corollary}" "\n"
                r"\begin{proof}" "\n"
                r"By Theorem B, the inner expression equals $n + 1$." "\n"
                r"\end{proof}" "\n"
            ))
            pdf = _write_source(root, "paper.pdf", b"%PDF-1.4\n")
            pkg = root / "lean"
            pkg.mkdir()
            (pkg / "lean-toolchain").write_text(pin + "\n", encoding="utf-8")
            (pkg / "lakefile.toml").write_text(
                'name = "Phase3bE2E"\n'
                '[[lean_lib]]\nname = "Prelude"\n'
                '[[lean_lib]]\nname = "Statements"\n'
                '[[lean_lib]]\nname = "Routine"\n'
                '[[lean_lib]]\nname = "Proofs"\n'
                '[[lean_lib]]\nname = "Assembly"\n',
                encoding="utf-8",
            )
            sources = {
                "Prelude.lean": "-- pure external imports\n",
                "Statements/Main.lean": (
                    "import Prelude\n"
                    "namespace LemA\ndef Statement : Prop := ∀ n : Nat, n + 0 = n\nend LemA\n"
                    "namespace ThmB\ndef Statement : Prop := ∀ n : Nat, (n + 0) + 1 = n + 1\nend ThmB\n"
                    "namespace CorC\ndef Statement : Prop := ∀ n : Nat, ((n + 0) + 1) + 0 = n + 1\nend CorC\n"
                ),
                "Routine/Glue.lean": (
                    "import Prelude\n"
                    "theorem add_one_cong {a b : Nat} (h : a = b) : a + 1 = b + 1 := congrArg (· + 1) h\n"
                ),
                "Proofs/A.lean": (
                    "import Statements.Main\nnamespace ProofsA\n"
                    "theorem main : LemA.Statement := Nat.add_zero\nend ProofsA\n"
                ),
                "Proofs/B.lean": (
                    "import Statements.Main\nimport Routine.Glue\nnamespace ProofsB\n"
                    "theorem step_1 (hA : LemA.Statement) (n : Nat) : n + 0 = n := hA n\n"
                    "theorem step_2 (hA : LemA.Statement) (n : Nat) : (n + 0) + 1 = n + 1 := add_one_cong (step_1 hA n)\n"
                    "theorem main (hA : LemA.Statement) : ThmB.Statement := fun n => step_2 hA n\n"
                    "end ProofsB\n"
                ),
                "Proofs/C.lean": (
                    "import Statements.Main\nnamespace ProofsC\n"
                    "theorem step_1 (hB : ThmB.Statement) (n : Nat) : (n + 0) + 1 = n + 1 := hB n\n"
                    "theorem step_2 (hB : ThmB.Statement) (n : Nat) : ((n + 0) + 1) + 0 = n + 1 :=\n"
                    "  (Nat.add_zero ((n + 0) + 1)).trans (step_1 hB n)\n"
                    "theorem main (hB : ThmB.Statement) : CorC.Statement := fun n => step_2 hB n\n"
                    "end ProofsC\n"
                ),
            }
            for rel, body in sources.items():
                _write_source(pkg, rel, body)

            env = os.environ.copy()
            lake = audit_lean.select_lake(pkg, pin, env, sys.stderr, offline=True)
            subprocess.run([*lake, "update"], cwd=pkg, env=env, check=True)

            _write_source(root, "steps/thm_b.json", json.dumps({
                "steps": [
                    {
                        "id": "s1", "lemma": "ProofsB.step_1", "step_deps": [],
                        "origin": "paper", "title": "Apply Lemma A",
                        "tex": r"Apply Lemma A to reduce $n + 0$ to $n$.",
                    },
                    {
                        "id": "s2", "lemma": "ProofsB.step_2", "step_deps": ["s1"],
                        "origin": "paper", "title": "Add 1 to both sides",
                        "tex": r"Add $1$ to both sides to conclude.",
                    },
                ],
                "main_deps": ["s2"],
            }, indent=2))
            _write_source(root, "steps/cor_c.json", json.dumps({
                "steps": [
                    {
                        "id": "s1", "lemma": "ProofsC.step_1", "step_deps": [],
                        "origin": "paper", "title": "Invoke Theorem B",
                        "tex": r"By Theorem B, the inner expression equals $n + 1$.",
                    },
                    {
                        "id": "s2", "lemma": "ProofsC.step_2", "step_deps": ["s1"],
                        "origin": "supplied", "title": "Drop trailing + 0",
                        "text": "Apply `Nat.add_zero` to simplify the outer `+ 0` omitted in the manuscript.",
                    },
                ],
                "main_deps": ["s2"],
            }, indent=2))
            _write_source(root, "reader.json", json.dumps({
                "schema_version": 1,
                "claims": {
                    "lem:a": {"reference": "Lemma 1"},
                    "thm:b": {"reference": "Theorem 2", "basis": "aligned"},
                    "cor:c": {"reference": "Corollary 3", "basis": "paper"},
                },
                "dependencies": [
                    {"claim": "thm:b", "prerequisite": "lem:a", "reason": "Uses Lemma 1"},
                    {"claim": "cor:c", "prerequisite": "thm:b", "reason": "Uses Theorem 2"},
                ],
            }, indent=2))

            project = {
                "schema_version": 1, "environments": ["lemma", "theorem", "corollary"],
                "edition": "test-v1", "title": "Phase 3b Live E2E",
                "tex": [tex], "pdf": pdf, "reader": "reader.json",
                "proof_work": {"mode": "paper"},
                "hosting": {
                    "decision": "github",
                    "repository": "https://github.com/example/phase3b-e2e",
                    "site": "https://example.github.io/phase3b-e2e/",
                    "visibility": "public",
                    "lean_ci": "enabled",
                    "lean_ci_level": "standard",
                },
                "work": {
                    "lem:a": {
                        "status": "drafted", "scope": "Lemma A.", "updated": "2026-11-26T00:00:00Z",
                        "assembly": {
                            "package": "lean", "module": "Proofs.A", "declaration": "ProofsA.main",
                            "expected": "LemA.Statement", "assumes": [],
                            "statements": ["Statements"], "statement_modules": ["Statements.Main"],
                        },
                    },
                    "thm:b": {
                        "status": "drafted", "scope": "Theorem B.", "updated": "2026-11-26T00:00:00Z",
                        "step_map": "steps/thm_b.json",
                        "assembly": {
                            "package": "lean", "module": "Proofs.B", "declaration": "ProofsB.main",
                            "expected": "ThmB.Statement", "assumes": ["lem:a"],
                            "statements": ["Statements"], "routine": ["Routine"],
                            "statement_modules": ["Statements.Main"],
                        },
                    },
                    "cor:c": {
                        "status": "drafted", "scope": "Corollary C.", "updated": "2026-11-26T00:00:00Z",
                        "step_map": "steps/cor_c.json",
                        "assembly": {
                            "package": "lean", "module": "Proofs.C", "declaration": "ProofsC.main",
                            "expected": "CorC.Statement", "assumes": ["thm:b"],
                            "statements": ["Statements"], "statement_modules": ["Statements.Main"],
                        },
                    },
                },
            }
            (root / "project.json").write_text(json.dumps(project, indent=2), encoding="utf-8")

            # 1. Assemble & audit: generates Assembly.lean and step_audit receipts for thm:b and cor:c.
            with redirect_stdout(io.StringIO()):
                atlas.assemble(root, run_audit=True)

            ev_b = json.loads((root / "evidence/assembly-thm_b.json").read_text(encoding="utf-8"))
            ev_c = json.loads((root / "evidence/assembly-cor_c.json").read_text(encoding="utf-8"))
            self.assertTrue(ev_b["step_audit"]["verified"])
            self.assertEqual(ev_b["step_audit"]["declaration"], "Assembly.thm_b")
            self.assertEqual(ev_b["step_audit"]["main_declaration"], "ProofsB.main")
            self.assertTrue(ev_c["step_audit"]["verified"])
            self.assertEqual(ev_c["step_audit"]["main_declaration"], "ProofsC.main")

            # 2. Commit and verify in CI (verify_ci.py).
            (root / "comparisons.json").write_text("{}\n", encoding="utf-8")
            head = _init_git_commit(root, "phase 3b e2e")
            ci_env = {
                "GITHUB_REPOSITORY": "example/phase3b-e2e",
                "GITHUB_SHA": head,
                "GITHUB_RUN_ID": "302",
                "GITHUB_RUN_ATTEMPT": "1",
            }
            with patch.dict(os.environ, ci_env, clear=False), redirect_stdout(io.StringIO()):
                ci_res = verify_ci.verify(root, offline=True, level="standard")

            self.assertIn("step_map_audit", ci_res["checks_enforced"])
            self.assertEqual(ci_res["claims"]["thm:b"]["step_badge"], "Step-verified (paper)")
            self.assertEqual(ci_res["claims"]["thm:b"]["step_map_sha256"], ev_b["step_audit"]["step_map_sha256"])
            self.assertEqual(ci_res["claims"]["cor:c"]["step_badge"], "Step-verified (with supplied steps)")
            self.assertEqual(ci_res["claims"]["cor:c"]["supplied_steps"], 1)
            self.assertNotIn("step_badge", ci_res["claims"]["lem:a"])

            # 3. Build & manifest with CI receipt confirm both badges & supplement.md.
            ci_file = root / "ci-receipt.json"
            ci_file.write_text(json.dumps(ci_res, indent=2), encoding="utf-8")
            with redirect_stdout(io.StringIO()):
                atlas.build(root, ci_receipt=ci_file, commit=head)
            man = atlas.manifest(root, ci_receipt=ci_file, commit=head)
            self.assertIn("Step-verified (paper)", man["markdown"])
            self.assertIn("Step-verified (with supplied steps)", man["markdown"])
            self.assertIn("ProofsC.step_2", (root / "dist/supplement.md").read_text(encoding="utf-8"))
            self.assertIn("Step-verified (paper)", (root / "dist/progress.html").read_text(encoding="utf-8"))
            self.assertIn("Step-verified (with supplied steps)", (root / "dist/progress.html").read_text(encoding="utf-8"))

            # 4. Tampering with a paper step's verbatim TeX fails CI loudly!
            bad_b = json.loads((root / "steps/thm_b.json").read_text(encoding="utf-8"))
            bad_b["steps"][0]["tex"] = "This line does not appear in paper.tex."
            (root / "steps/thm_b.json").write_text(json.dumps(bad_b), encoding="utf-8")
            with patch.dict(os.environ, ci_env, clear=False), redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError, "not a verbatim substring of the bound TeX sources"):
                    verify_ci.verify(root, offline=True, level="standard")


if __name__ == "__main__":
    unittest.main()
