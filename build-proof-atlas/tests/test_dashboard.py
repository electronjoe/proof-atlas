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
