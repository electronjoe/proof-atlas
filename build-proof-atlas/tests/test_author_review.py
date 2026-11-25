from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import atlas
import author_review as review


class StatementApproval(unittest.TestCase):
    def setUp(self):
        folder = tempfile.TemporaryDirectory()
        self.addCleanup(folder.cleanup)
        self.root = root = Path(folder.name).resolve()

        def source(name, data):
            (root / name).write_bytes(data)
            return {"path": name, "sha256": hashlib.sha256(data).hexdigest()}

        tex = source("paper.tex", rb"\begin{theorem}\label{t}The rate at zero is positive.\end{theorem}")
        (root / "lean").mkdir()
        self.lean = source("lean/T.lean", b"def rate (n : Nat) := n + 1\ndef Statement : Prop := rate 0 > 0\n"
                                          b"theorem result : Statement := Nat.zero_lt_one\n")
        (root / "run.log").write_bytes(b"Built T\n")
        self.receipt({"rate": "a" * 64, "Statement": "b" * 64})
        self.project = {
            "schema_version": 1, "environments": ["theorem"], "edition": "test", "title": "Test paper",
            "tex": [tex], "pdf": source("paper.pdf", b"test"), "proof_work": {"mode": "paper"},
            "hosting": {"decision": "local"},
            "work": {"t": {"status": "closed", "scope": "Result.", "run_log": "run.log",
                           "checked_inputs": {self.lean["path"]: self.lean["sha256"]},
                           "closure": {"expected": "Statement", "declaration": "result", "package": "lean",
                                       "audit": "audit.json", "correspondence": "Result."}}},
        }
        (root / "project.json").write_text(json.dumps(self.project), encoding="utf-8")

    def receipt(self, digests, statement=True):
        constants = [{"name": n, "file": "T.lean", "lines": [i + 1, i + 1], "sha256": d}
                     for i, (n, d) in enumerate(sorted(digests.items()))]
        audit = {"expected": "Statement", "declaration": "result", "axioms": [], "toolchain": "test-pin",
                 "checked_inputs": {"T.lean": self.lean["sha256"]}}
        if statement:
            audit["statement"] = {"expected": "Statement", "constants": constants, "sha256": hashlib.sha256(
                "".join(f'{c["name"]} {c["sha256"]}\n' for c in constants).encode()).hexdigest()}
        (self.root / "audit.json").write_text(json.dumps(audit), encoding="utf-8")


    def packet(self):
        return review.get_packet(self.root,"t")

    def compare(self, result="match", default_assessments=None, **updates):
        record = dict(bindings=self.packet()["view"]["bindings"], result=result, paper_reading="For n=0 the rate is positive.",
                      lean_reading="The rate at zero exceeds zero.", paper_refs="paper.tex, theorem t", lean_refs="Statement and rate")
        record["analysis"] = dict(summary="Compare the rate at zero.", scope="Only n=0 is asserted.",
                                  cases=[dict(case="Zero", paper="Positive", lean="0 < rate 0", why="rate 0 = 1", kind="agrees")],
                                  advice="Check the value at zero.")
        if result != "match":
            record["analysis"]["suggested_feedback"] = "Please clarify the domain at zero."
        if default_assessments is not None:
            record["analysis"]["default_assessments"] = default_assessments
        record.update(updates)
        review.save_comparison(self.root,"t",record)

    def test_default_assessments_follow_the_current_scan(self):
        from review_web import render
        self.compare()  # Existing comparison predates the scan.
        path = self.root / "audit.json"
        audit = json.loads(path.read_bytes())
        use = dict(constant="constrainedRate", file="T.lean", lines=[1, 1])
        audit["defaults"] = [dict(use, construct="Real.log"), dict(use, construct="InfSet.sInf")]
        path.write_text(json.dumps(audit), encoding="utf-8")
        packet = self.packet()
        log_id, inf_id = [item["id"] for item in packet["defaults"]]
        self.assertNotEqual(log_id, inf_id)
        self.assertEqual(render(packet).count(b"<strong>not assessed</strong>"), 2)
        analysis = packet["view"]["analysis"]
        explained = dict(status="justified", explanation="The hypothesis 0 < p gives a positive argument.")
        question = dict(status="needs attention", explanation="What ensures a nonempty set bounded below?")
        saved = (self.root / "comparisons.json").read_bytes()
        for invalid in ({}, {log_id: explained}, {log_id: explained, "obsolete": question},
                        {log_id: explained, inf_id: dict(question, status="not assessed")},
                        {log_id: explained, inf_id: dict(question, explanation=" ")}):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                self.compare(analysis=dict(analysis, default_assessments=invalid))
            self.assertEqual((self.root / "comparisons.json").read_bytes(), saved)
        self.compare(analysis=dict(analysis, default_assessments={log_id: explained, inf_id: question}))
        # Reordering and moving a definition do not detach its explanation.
        audit["defaults"].reverse()
        audit["defaults"][0]["lines"] = [2, 2]
        path.write_text(json.dumps(audit), encoding="utf-8")
        packet = self.packet()
        self.assertTrue(packet["checked"])
        with redirect_stdout(io.StringIO()):
            atlas.build(self.root)
        static = (self.root / "dist" / review.review_url("t")).read_text(encoding="utf-8")
        local = render(packet, secret="local").decode()
        for page in (static, local):
            self.assertLess(page.index(question["explanation"]), page.index("How the statements compare"))
            details = page.split("<details><summary>Show explained uses</summary>", 1)
            self.assertIn(question["explanation"], details[0])
            self.assertIn("InfSet.sInf", details[0])
            self.assertIn("Real.log", details[1].split("</details>", 1)[0])
            self.assertIn(atlas.esc(explained["explanation"]), details[1].split("</details>", 1)[0])
        dashboard = (self.root / "dist/progress.html").read_text(encoding="utf-8")
        self.assertIn("Lean checked", dashboard)
        self.assertIn("1 of 1 stated results closed", dashboard)
        audit["defaults"].append(dict(use, construct="Real.sqrt"))
        path.write_text(json.dumps(audit), encoding="utf-8")
        self.assertEqual(render(self.packet()).count(b"<strong>not assessed</strong>"), 1)

    def test_project_witness_search_and_claim_exception(self):
        path = self.root / "project.json"
        work = self.project["work"]["t"]

        def plan():
            path.write_text(json.dumps(self.project), encoding="utf-8")
            return atlas.review_work(self.root)["witness_search"]["t"]

        self.assertEqual(plan()["mode"], "available")
        work["witness_missing_result"] = "Existence of an interior differentiability point"
        self.assertEqual(plan()["action"], "defer missing result")
        self.assertEqual(plan()["missing_result"], work["witness_missing_result"])
        self.project["witness_search"] = "skip"
        self.assertEqual(plan()["action"], "skip search")
        work["witness_search"] = "pursue"
        self.assertEqual(plan()["action"], "pursue missing result")
        del work["witness_search"]
        self.assertEqual(plan()["action"], "skip search")
        self.project["witness_search"] = "pursue"
        self.assertEqual(plan()["action"], "pursue missing result")

        receipt_path = self.root / "audit.json"
        audit = json.loads(receipt_path.read_bytes())
        audit["hypotheses"] = {"declaration": "example_holds", "proposition": "True", "axioms": []}
        receipt_path.write_text(json.dumps(audit), encoding="utf-8")
        saved = receipt_path.read_bytes()
        self.project["witness_search"] = "skip"
        self.assertEqual(plan(), {"mode": "skip", "action": "reuse checked witness"})
        with redirect_stdout(io.StringIO()):
            atlas.build(self.root)
        self.assertEqual(receipt_path.read_bytes(), saved)
        self.assertEqual(self.packet()["witness"]["declaration"], "example_holds")

    def test_optional_and_versioned_review(self):
        self.receipt({"Statement":"a"*64, "rate":"b"*64})
        self.compare()
        initial=self.packet()
        with patch.object(sys.stdin,"isatty",return_value=True),redirect_stdout(io.StringIO()):
            review.terminal(self.root,["t"],"Demo reviewer",ask=lambda prompt:"")
        self.assertFalse(self.packet()["events"])
        review.decide(self.root,"t",initial["token"],"approve","Demo reviewer")
        self.assertTrue(self.packet()["approved"])
        with self.assertRaisesRegex(ValueError,"Reload"):
            review.decide(self.root,"t",initial["token"],"difference","Second reader","Check n=0")
        self.receipt({"Statement":"a"*64, "rate":"b"*64})
        self.assertTrue(self.packet()["approved"])
        self.compare(lean_reading="The audited conclusion concerns the value at zero.")
        self.assertFalse(self.packet()["approved"])
        self.assertIn("exceeds zero",self.packet()["events"][0]["view"]["lean_reading"])
        self.receipt({"Statement":"a"*64, "rate":"c"*64})
        self.assertFalse(self.packet()["ready"])
        self.assertEqual(self.packet()["assessment"],"Comparison pending")

    def test_discrepancy_resolution_and_counts(self):
        self.receipt({"Statement":"a"*64})
        for result,issue in [("difference","Only the upper bound is checked."),("difference","Different walk."),
                             ("unsure","Unclear boundary case.")]:
            self.compare(result,issue=issue,actor="Author" if result=="unsure" else "Proof agent",next="Resolve the stated gap.")
            self.assertTrue(self.packet()["disputed"])
            self.assertEqual(self.packet()["issue"],issue)
        self.compare(resolution="Corrected the theorem and checked both cases.")
        review.decide(self.root,"t",self.packet()["token"],"difference","Test author","The display says all n.")
        with redirect_stdout(io.StringIO()):
            atlas.build(self.root)
        page=(self.root/"dist/progress.html").read_text(encoding="utf8")
        self.assertIn("0 of 1 stated results closed",page)
        self.assertIn("Lean checked",page)
        event=self.packet()["events"][-1]["id"]
        self.compare(resolves=[event],resolution="Corrected the display to n=0.")
        self.assertTrue(self.packet()["ready"])
        with patch.object(sys.stdin,"isatty",return_value=True),redirect_stdout(io.StringIO()):
            review.terminal(self.root,["t"],"Test author",ask=lambda prompt:"t")
            atlas.build(self.root)
        self.assertTrue(self.packet()["approved"])
        self.assertIn("1/1 author reviewed",(self.root/"dist/progress.html").read_text(encoding="utf8"))
        self.assertEqual(self.packet()["events"][-1]["decision"],"approve")

    def test_explanation_is_versioned_and_advice_tracks_feedback(self):
        from review_web import render
        self.compare()
        packet = self.packet()
        review.decide(self.root,"t",packet["token"],"approve","Test author")
        revised = dict(packet["view"]["analysis"], advice="Approve for the zero input only.")
        self.compare(analysis=revised)
        self.assertFalse(self.packet()["approved"])
        self.assertNotEqual(self.packet()["events"][0]["view"]["analysis"],revised)
        self.assertIn(b"Approve for the zero input only.",render(self.packet()))
        review.decide(self.root,"t",self.packet()["token"],"difference","Author","Does this include other inputs?")
        self.assertNotIn(b"Approve for the zero input only.",render(self.packet()).split(b"<h2>Review history</h2>")[0])
        self.compare("unsure",issue="Scope unclear",actor="Proof agent",next="Check the domain")
        with self.assertRaises(ValueError):
            self.compare("unsure",analysis=revised,issue="Scope unclear",actor="Proof agent",next="Check the domain")

    def test_legacy_comparison_and_changed_sources(self):
        self.compare()
        path = self.root/"comparisons.json"
        records = json.loads(path.read_bytes())
        del records["t"]["analysis"]
        path.write_text(json.dumps(records),encoding="utf-8")
        self.assertFalse(self.packet()["ready"])
        self.assertIn("justification",self.packet()["next"])
        self.compare()
        self.receipt({"Statement":"c"*64})
        self.assertNotIn("analysis",self.packet()["view"])

    def test_difference_kinds(self):
        from review_web import render
        self.compare()
        legacy = json.loads((self.root/"comparisons.json").read_bytes())
        del legacy["t"]["analysis"]["cases"][0]["kind"]
        (self.root/"comparisons.json").write_text(json.dumps(legacy), encoding="utf-8")
        review.decide(self.root, "t", self.packet()["token"], "approve", "Author")
        # A record saved before kinds existed keeps its approval and displays as not classified.
        old = self.packet()
        self.assertTrue(old["approved"])
        self.assertIn(b"<small>not classified</small>", render(old))
        def build():
            with redirect_stdout(io.StringIO()):
                atlas.build(self.root)
            data = (self.root/"dist/proofs/index.html").read_text(encoding="utf-8")
            return (self.root/"dist/progress.html").read_text(encoding="utf-8"), data
        page, data = build()
        self.assertIn('"differences": null', data)
        self.assertNotIn("from the paper</a>", page)
        # New records must classify every case, with a known kind.
        analysis = old["view"]["analysis"]
        with self.assertRaisesRegex(ValueError, "Give each case a kind"):
            self.compare(analysis=analysis)
        with self.assertRaisesRegex(ValueError, "Give each case a kind"):
            self.compare(analysis=dict(analysis, cases=[dict(analysis["cases"][0], kind="weaker")]))
        self.compare()
        self.assertNotEqual(self.packet()["version"], old["version"])
        self.assertFalse(self.packet()["approved"])
        page, data = build()
        self.assertIn('"differences": []', data)
        self.assertIn("No differences from the paper", page)
        extra = dict(case="Negative", paper="Not stated", lean="Also for n < 0", why="Lean covers more", kind="stronger")
        self.compare(analysis=dict(analysis, cases=[dict(analysis["cases"][0], kind="agrees"), extra]))
        page, data = build()
        self.assertIn("1 difference from the paper", page)
        self.assertIn('"differences": [{"case": "Negative"', data)
        self.assertIn(b"<small>stronger</small>", render(self.packet()))

    def test_manuscript_edits_can_be_cleared_and_restored_independently(self):
        import manuscript_edits as edits
        self.compare()
        review.decide(self.root,"t",self.packet()["token"],"approve","Author",paper_edit="Use explicit inequality.")
        first = self.packet()["events"][-1]["id"]
        path = self.root/"manuscript-edits.json"
        path.write_text(json.dumps({"version":1,"edits":{"typo":{"claim":"t","edition":"test","reason":"Typo"}}}))
        def apply(action, selected):
            edits.update(self.root,edits.token(*edits.inventory(self.root)),action,selected)
        old = edits.token(*edits.inventory(self.root))
        apply("clear",[first])
        with self.assertRaisesRegex(ValueError,"Reload"):
            edits.update(self.root,old,"clear-all",[])
        self.assertIn(b"Active (1)",edits.render(self.root))
        apply("clear-all",[])
        self.assertIn(b"Cleared (2)",edits.render(self.root))
        apply("restore",[first,"typo"])
        apply("request",[first])
        self.assertEqual(edits.inventory(self.root)[1][first]["status"],"Draft requested")
        self.assertTrue(self.packet()["approved"])

    def test_optional_stronger_result_and_reviewer_scope(self):
        from review_web import render
        self.compare()
        p = self.packet()
        review.decide(self.root,"t",p["token"],"approve","Author",scope_note="I approve the conclusion at zero.")
        self.compare(stronger_result="The optimizing witness is also unique.")
        p = self.packet()
        self.assertTrue(p["approved"])
        self.assertIn(b"The optimizing witness is also unique.",render(p))
        self.assertEqual(p["author_scope"],"I approve the conclusion at zero.")
        with self.assertRaises(ValueError):
            self.compare("difference",stronger_result="Extra",issue="A case is missing",actor="Proof agent",next="Prove it.")
        review.decide(self.root,"t",p["token"],"difference","Reader","Please check the endpoint.")
        self.assertFalse(self.packet()["stronger_result"])
        self.assertFalse(self.packet()["author_scope"])

    def test_review_work_follows_feedback_without_requiring_approval(self):
        self.compare("unsure",issue="Boundary omitted",actor="Proof agent",next="Check the endpoint")
        (self.root/"scratch.lean").write_text("-- A local experiment")
        report=atlas.review_work(self.root)
        self.assertEqual(report["agent_tasks"][0]["next"],"Check the endpoint")
        self.compare("unsure",issue="Two intended domains",actor="Author",next="Which domain did you intend?")
        self.assertFalse(atlas.review_work(self.root)["agent_tasks"])
        self.assertTrue(atlas.review_work(self.root)["author_questions"])
        self.compare(resolution="Covered both domains.")
        review.decide(self.root,"t",self.packet()["token"],"difference","Reader","What about zero?")
        self.assertIn("zero",atlas.review_work(self.root)["agent_tasks"][0]["issue"])
        self.compare(resolves=[self.packet()["events"][-1]["id"]],resolution="Checked the zero case.")
        self.assertFalse(self.packet()["approved"])
        self.assertFalse(atlas.review_work(self.root)["agent_tasks"])

    def test_release_check_requires_committed_comparison_and_current_ci(self):
        self.project["hosting"] = {"lean_ci":"enabled","repository":"https://github.com/example/atlas"}
        (self.root/"project.json").write_text(json.dumps(self.project),encoding="utf8")
        self.compare()
        def git(*args):
            return subprocess.check_output(["git","-c","user.name=Test","-c","user.email=test@example.com",*args],
                                           cwd=self.root,text=True).strip()
        git("init","-q")
        git("add",".")
        git("commit","-qm","Checked release")
        receipt_path = self.root/"remote.json"
        def status():
            return atlas.review_work(self.root,require_ci=True,ci_receipt=receipt_path)
        self.assertEqual(status()["ci_pending"],["t"])
        record = {"repository":"example/atlas","commit":git("rev-parse","HEAD"),"run_id":42,"attempt":1,
                  "claims":{"t":{"audit_sha256":hashlib.sha256((self.root/"audit.json").read_bytes()).hexdigest(),
                                 "statement_sha256":self.packet()["view"]["bindings"]["statement"]}}}
        receipt_path.write_text(json.dumps(record))
        self.assertFalse(status()["ci_pending"])
        self.compare(lean_reading="An updated reading that is still only local.")
        self.assertTrue(status()["uncommitted_delivery_files"])
        git("add","comparisons.json")
        git("commit","-qm","Updated review")
        self.assertEqual(status()["ci_pending"],["t"])

    def test_review_inputs_includes_witness_snippet(self):
        from review_web import render
        (self.root / "lean/Examples.lean").write_text("import T\ntheorem nonempty_case : True := trivial\n", encoding="utf-8")
        audit = json.loads((self.root / "audit.json").read_bytes())
        audit["hypotheses"] = {"declaration": "nonempty_case", "proposition": "True", "axioms": [],
                               "file": "Examples.lean", "lines": [2, 2]}
        (self.root / "audit.json").write_text(json.dumps(audit), encoding="utf-8")
        script = Path(__file__).resolve().parents[1] / "scripts/atlas.py"
        lean_side = json.loads(subprocess.check_output(
            [sys.executable, str(script), "review-inputs", str(self.root), "t", "--side", "lean"], text=True))
        self.assertEqual(lean_side["witness"], {
            "declaration": "nonempty_case", "proposition": "True",
            "file": "Examples.lean", "lines": [2, 2], "text": "theorem nonempty_case : True := trivial",
        })
        paper_side = json.loads(subprocess.check_output(
            [sys.executable, str(script), "review-inputs", str(self.root), "t", "--side", "paper"], text=True))
        self.assertNotIn("witness", paper_side)
        html_page = render(self.packet()).decode("utf-8")
        self.assertIn("Inspect the checked hypotheses example · nonempty_case · Examples.lean L2", html_page)
        self.assertIn("theorem nonempty_case : True := trivial", html_page)

    def test_gate1_statement_review_and_carryover(self):
        from review_web import queue, render
        stmt_text = b"def rate (n : Nat) := n + 1\ndef Statement : Prop := rate 0 > 0\n"
        (self.root / "lean/Statements.lean").write_bytes(stmt_text)
        (self.root / "lean/Examples.lean").write_text("import Statements\ntheorem ex : True := trivial\n", encoding="utf-8")
        stmt_sha = hashlib.sha256(stmt_text).hexdigest()
        ex_sha = hashlib.sha256((self.root / "lean/Examples.lean").read_bytes()).hexdigest()
        constants = [
            {"name": "Statement", "file": "Statements.lean", "lines": [2, 2], "sha256": "b" * 64},
            {"name": "rate", "file": "Statements.lean", "lines": [1, 1], "sha256": "a" * 64},
        ]
        stmt_digest = hashlib.sha256("".join(f'{c["name"]} {c["sha256"]}\n' for c in constants).encode()).hexdigest()
        stmt_audit = {
            "statement_only": True, "expected": "Statement", "axioms": [], "toolchain": "test-pin",
            "statements": ["Statements"],
            "checked_inputs": {"Statements.lean": stmt_sha, "Examples.lean": ex_sha},
            "statement": {"expected": "Statement", "constants": constants, "sha256": stmt_digest},
            "defaults": [{"constant": "rate", "file": "Statements.lean", "lines": [1, 1], "construct": "HSub.hSub", "type": "Nat"}],
            "hypotheses": {"declaration": "ex", "proposition": "True", "axioms": [], "file": "Examples.lean", "lines": [2, 2]},
        }
        (self.root / "stmt-audit.json").write_text(json.dumps(stmt_audit), encoding="utf-8")
        self.project["work"]["t"] = {
            "status": "drafted", "summary": "Drafted statement.", "step": "Gate 1 statement check.",
            "next": "Prove t.", "updated": "2026-11-23T00:00:00Z",
            "statement_check": {"audit": "stmt-audit.json", "package": "lean", "expected": "Statement"},
        }
        (self.root / "project.json").write_text(json.dumps(self.project), encoding="utf-8")

        # Before comparison, review-work flags Gate 1 comparison as an agent task.
        self.assertEqual(atlas.review_work(self.root)["agent_tasks"][0]["claim"], "t")

        # review-inputs --side lean surfaces statement sources, defaults, and witness pre-closure.
        script = Path(__file__).resolve().parents[1] / "scripts/atlas.py"
        lean_side = json.loads(subprocess.check_output(
            [sys.executable, str(script), "review-inputs", str(self.root), "t", "--side", "lean"], text=True))
        self.assertEqual([s["name"] for s in lean_side["lean"]], ["Statement", "rate"])
        self.assertEqual(lean_side["defaults"][0]["construct"], "HSub.hSub")
        self.assertEqual(lean_side["witness"]["declaration"], "ex")

        # The question is saved for immediate discussion or later review.
        flag = lean_side["defaults"][0]["id"]
        assessments = {flag: {"status": "justified", "explanation": "The definition uses truncated natural subtraction."}}
        with self.assertRaisesRegex(ValueError, "one assessment"):
            self.compare("unsure", issue="Endpoint ambiguous", actor="Author", next="Confirm whether n=0 is included.")
        self.compare("unsure", default_assessments=assessments, issue="Endpoint ambiguous",
                     actor="Author", next="Confirm whether n=0 is included.")
        work_report = atlas.review_work(self.root)
        self.assertFalse(work_report["agent_tasks"])
        self.assertEqual(work_report["author_questions"][0]["issue"], "Endpoint ambiguous")

        # Once Gate 1 matches, the review page labels it "Statement drafted (proof in progress)" and supports pre-approval.
        self.compare("match", default_assessments=assessments, resolution="Author confirmed n=0 is included.")
        pkt = self.packet()
        self.assertTrue(pkt["statement_checked"])
        self.assertFalse(pkt["checked"])
        self.assertTrue(pkt["ready"])
        self.assertFalse(atlas.review_work(self.root)["agent_tasks"])
        with redirect_stdout(io.StringIO()):
            atlas.build(self.root)
        self.assertIn("Statement drafted (proof in progress)", (self.root / "dist/progress.html").read_text(encoding="utf-8"))
        self.assertIn(b"Statement drafted (proof in progress)", render(pkt))
        self.assertIn(b"Statement drafted (proof in progress)", queue([pkt]))

        review.decide(self.root, "t", pkt["token"], "approve", "Author", scope_note="Matches paper.")
        pkt = self.packet()
        self.assertTrue(pkt["preapproved"])
        self.assertFalse(pkt["approved"])
        self.assertIn(b"Statement approved (proof in progress)", render(pkt))

        # Closing the claim with the SAME statement.sha256 carries both comparison and approval over automatically!
        self.receipt({"rate": "a" * 64, "Statement": "b" * 64})
        self.project["work"]["t"] = {
            "status": "closed", "scope": "Result.", "run_log": "run.log",
            "checked_inputs": {self.lean["path"]: self.lean["sha256"]},
            "closure": {"expected": "Statement", "declaration": "result", "package": "lean",
                        "audit": "audit.json", "correspondence": "Result."},
        }
        (self.root / "project.json").write_text(json.dumps(self.project), encoding="utf-8")
        closed_pkt = self.packet()
        self.assertTrue(closed_pkt["checked"])
        self.assertTrue(closed_pkt["approved"])
        self.assertFalse(closed_pkt["preapproved"])
        self.assertEqual(closed_pkt["author_scope"], "Matches paper.")

        # If Statements/ changed during proof search (different statement.sha256), approval & comparison invalidate.
        self.receipt({"rate": "c" * 64, "Statement": "b" * 64})
        drifted = self.packet()
        self.assertFalse(drifted["approved"])
        self.assertEqual(drifted["assessment"], "Comparison pending")

    def test_weaker_conclusion_cannot_match_and_surfaces_metadata(self):
        from review_web import render
        path = self.root / "audit.json"
        audit = json.loads(path.read_bytes())
        audit["axioms"] = ["Classical.choice", "propext", "Quot.sound"]
        audit["axiom_profile"] = "Standard classical axioms (Classical.choice, Quot.sound, propext)"
        audit["external_packages"] = [
            {"name": "mathlib", "rev": "a" * 40, "url": "https://github.com/leanprover-community/mathlib4",
             "direct": True, "third_party": False},
            {"name": "riemann-roch", "rev": "b" * 40, "url": "https://github.com/example/riemann-roch",
             "direct": True, "third_party": True},
        ]
        for const in audit["statement"]["constants"]:
            if const["name"] == "rate":
                const["noncomputable"] = True
                const["pp_no_notation"] = "Nat → Nat := fun n => HAdd.hAdd n 1"
            else:
                const["noncomputable"] = False
                const["pp_no_notation"] = "Prop := GT.gt (rate 0) 0"
        path.write_text(json.dumps(audit), encoding="utf-8")

        # weaker conclusion is rejected when result == "match".
        weaker_case = dict(case="C2: runtime bound", paper="O(n log n) algorithm", lean="Existence only (noncomputable)",
                           why="Lean proves existence without runtime complexity.", kind="weaker conclusion")
        bad_analysis = dict(summary="Omitted algorithmic bound.", scope="Existence only.",
                            cases=[weaker_case], advice="Keep claim open until runtime bound is proved.",
                            suggested_feedback="Should the runtime bound remain an open obligation?")
        with self.assertRaisesRegex(ValueError, "weaker conclusion cannot be recorded as a match"):
            self.compare("match", analysis=bad_analysis)

        # Accepted with result == "difference"; keeps closed_results at 0 on dashboard.
        self.compare("difference", analysis=bad_analysis, issue="Runtime bound omitted.",
                     actor="Proof agent", next="Track runtime bound as an open subproof.")
        pkt = self.packet()
        self.assertTrue(pkt["disputed"])
        self.assertEqual(pkt["noncomputable_constants"], ["rate"])
        self.assertIn("Standard classical axioms", pkt["axiom_profile"])

        # review-inputs --side lean carries noncomputable, pp_no_notation, external_packages, and axiom_profile.
        script = Path(__file__).resolve().parents[1] / "scripts/atlas.py"
        lean_side = json.loads(subprocess.check_output(
            [sys.executable, str(script), "review-inputs", str(self.root), "t", "--side", "lean"], text=True))
        self.assertEqual(lean_side["noncomputable_constants"], ["rate"])
        self.assertIn("Standard classical axioms", lean_side["axiom_profile"])
        self.assertEqual([p["name"] for p in lean_side["external_packages"] if p["third_party"]], ["riemann-roch"])
        by_name = {s["name"]: s for s in lean_side["lean"]}
        self.assertTrue(by_name["rate"]["noncomputable"])
        self.assertIn("HAdd.hAdd", by_name["rate"]["pp_no_notation"])
        self.assertIn("GT.gt", by_name["Statement"]["pp_no_notation"])

        # Review HTML and built Explorer payload surface all Phase 2a metadata and weaker conclusion.
        html_page = render(pkt).decode("utf-8")
        self.assertIn("<small>weaker conclusion</small>", html_page)
        self.assertIn("Noncomputable definitions in statement:", html_page)
        self.assertIn("Third-party external dependencies", html_page)
        self.assertIn("riemann-roch", html_page)
        self.assertNotIn("mathlib4", html_page)
        self.assertIn("Notation-free Lean signature (pp.notation false)", html_page)
        self.assertIn("HAdd.hAdd", html_page)
        self.assertIn("Standard classical axioms", html_page)

        with redirect_stdout(io.StringIO()):
            atlas.build(self.root)
        dashboard = (self.root / "dist/progress.html").read_text(encoding="utf-8")
        self.assertIn("0 of 1 stated results closed", dashboard)
        self.assertIn("1 difference from the paper", dashboard)
        explorer = (self.root / "dist/proofs/index.html").read_text(encoding="utf-8")
        self.assertIn('"noncomputable_constants": ["rate"]', explorer)
        self.assertIn('"unfolded_signatures":', explorer)
        self.assertIn("riemann-roch", explorer)
