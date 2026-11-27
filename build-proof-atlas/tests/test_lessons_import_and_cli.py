"""Tests for v0.12.0 lessons: import/inventory (#1-#6), prose lint (#19), handoff (#12), and release-check (#15)."""
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
import import_arxiv


def _write(root: Path, rel: str, data) -> dict:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = data.encode("utf-8") if isinstance(data, str) else data
    path.write_bytes(raw)
    return {"path": rel, "sha256": hashlib.sha256(raw).hexdigest()}


class LessonsImportInventoryAndCliTests(unittest.TestCase):
    def test_parse_newtheorems_nested_braces_and_wrappers(self):
        tex = r"""
\newtheorem{thm}{\textbf{Theorem}}
\newtheorem{coro}[thm]{\textnormal{\emph{Corollary}}}
\newtheorem*{prop}{\textrm{Proposition}}
\newtheorem{lem}{{\bfseries Lemma}}[section]
\newtheorem{rem}{\textbf{Remark}}
"""
        parsed = import_arxiv.parse_newtheorems(tex)
        by_env = {env: (printed, canon) for env, printed, canon in parsed}
        self.assertEqual(by_env["thm"], ("Theorem", "theorem"))
        self.assertEqual(by_env["coro"], ("Corollary", "corollary"))
        self.assertEqual(by_env["prop"], ("Proposition", "proposition"))
        self.assertEqual(by_env["lem"], ("Lemma", "lemma"))
        self.assertNotIn("rem", by_env)

    def test_headline_kinds_aliases_and_environment_kinds(self):
        for env in ("theorem", "thm", "corollary", "cor", "coro", "proposition", "prop", "main"):
            self.assertEqual(atlas.claim_tier({"id": "c1", "kind": env}), "headline")
        self.assertEqual(atlas.claim_tier({"id": "c2", "kind": "lemma"}), "supporting")
        # Explicit environment_kinds overrides custom env name.
        self.assertEqual(
            atlas.claim_tier({"id": "c3", "kind": "mybig"}, env_kinds={"mybig": "theorem"}),
            "headline",
        )
        self.assertEqual(
            atlas.claim_tier({"id": "c4", "kind": "myconj"}, env_kinds={"myconj": "conjecture"}),
            "conjecture",
        )

    def test_atlas_init_in_existing_repo_and_atomic_umask(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            tex_body = (
                "\\documentclass{IEEEtran}\n"
                "\\newtheorem{thm}{\\textbf{Theorem}}\n"
                "\\begin{document}\n"
                "\\begin{thm}[Main Bound]\\label{thm:main}\n"
                "Delay is bounded.\n"
                "\\end{thm}\n"
                "Brief commentary paragraph explaining the constants.\n"
                "\\begin{proof} (Theorem \\ref{thm:main})\n"
                "Follows immediately.\n"
                "\\end{proof}\n"
                "\\end{document}\n"
            )
            _write(root, "paper/main.tex", tex_body)
            _write(root, "paper/paper.pdf", b"%PDF-1.4\n%%EOF\n")
            _write(root, "references/companion.tex", "Line 1\nCompanion proof line 2\nCompanion proof line 3\n")

            with patch.object(import_arxiv, "pdf_pages", return_value=[]):
                res = atlas.init_project(
                    root,
                    tex_paths=["paper/main.tex"],
                    pdf_path="paper/paper.pdf",
                    title="LIFO Delay Study",
                    edition="arXiv:1008.4895v2",
                    publication="https://arxiv.org/abs/1008.4895v2",
                    authors=["Alice Smith", "Bob Jones"],
                    citation_details="2010",
                )
            self.assertEqual(res["claims"], 1)
            self.assertEqual(res["environment_kinds"].get("thm"), "theorem")
            proj = json.loads((root / "project.json").read_text(encoding="utf-8"))
            self.assertEqual(proj["tex"][0]["path"], "paper/main.tex")
            self.assertEqual(proj["pdf"]["path"], "paper/paper.pdf")
            self.assertEqual(proj["environment_kinds"]["thm"], "theorem")

            # #4: Inventory captured proof across brief commentary paragraph referencing \ref{thm:main}.
            inv = json.loads((root / "dist/inventory.json").read_text(encoding="utf-8"))
            self.assertTrue(inv[0]["adjacent_proof"])
            self.assertIn("\\begin{proof}", inv[0]["excerpt"])

            # #6: atomic() respects umask rather than leaving 0600.
            mode = stat.S_IMODE((root / "dist/progress.html").stat().st_mode)
            self.assertEqual(mode, atlas._default_file_mode())
            self.assertNotEqual(mode, 0o600)

            # Refuses to overwrite existing project.json without --force.
            with self.assertRaisesRegex(ValueError, "project.json already exists"):
                atlas.init_project(
                    root, tex_paths=["paper/main.tex"], pdf_path="paper/paper.pdf", title="Again"
                )

            # #4: Detached proof via reader.json proof_source appears in build payload and review-inputs.
            reader = json.loads((root / "reader.json").read_text(encoding="utf-8"))
            reader["claims"]["thm:main"] = {
                "reference": "Theorem 1",
                "summary": "Queue delay is bounded by delta_max and V^{log V}.",
                "proof_source": {"path": "references/companion.tex", "lines": [2, 3]},
            }
            (root / "reader.json").write_text(json.dumps(reader, indent=2), encoding="utf-8")

            out_buf = io.StringIO()
            with patch.object(sys, "stdout", out_buf):
                atlas.build(root)
            printed = out_buf.getvalue()
            # #19: Warns about missing sketch and raw ASCII math in summary.
            self.assertIn("no 'sketch'", printed)
            self.assertIn("raw ASCII math" if "raw ASCII math" in printed else "unescaped ASCII math", printed)
            self.assertIn("delta_max", printed)

            rw = atlas.review_work(root)
            kinds = {w["kind"] for w in rw.get("reader_warnings", [])}
            self.assertEqual(kinds, {"missing_sketch", "raw_ascii_math"})

            # Check detached proof embedded in explorer payload.
            explorer_html = (root / "dist/proofs/index.html").read_text(encoding="utf-8")
            self.assertIn("Companion proof line 2", explorer_html)
            self.assertIn("references/companion.tex L2–3", explorer_html)

            # #12: handoff generates HANDOFF.md and copy-paste resume prompt.
            h_res = atlas.generate_handoff(root, write=True)
            self.assertTrue((root / "HANDOFF.md").is_file())
            self.assertIn("DO NOT edit `Statements/`", h_res["resume_prompt"])
            self.assertIn("Theorem 1", h_res["markdown"])

            # #15: release-check flags missing front-door files, then passes once added.
            rc_fail = atlas.release_check(root)
            self.assertFalse(rc_fail["ready"])
            self.assertIn("readme_exists", rc_fail["missing_required"])
            self.assertIn("license_file", rc_fail["missing_required"])
            self.assertIn("citation_cff", rc_fail["missing_required"])

            _write(root, "README.md", (
                "# LIFO Delay\n\n"
                "Reproduce with `lake build`.\n"
                "AI-assisted formalization disclosure: built with LLM assistance.\n"
            ))
            _write(root, "LICENSE", "MIT License\n")
            _write(root, "CITATION.cff", "cff-version: 1.2.0\ntitle: LIFO Delay\n")
            rc_ok = atlas.release_check(root)
            self.assertTrue(rc_ok["ready"])
            self.assertEqual(rc_ok["missing_required"], [])

    def test_pdf_pages_warns_when_extractors_absent(self):
        with tempfile.TemporaryDirectory() as tmp:
            pdf = Path(tmp) / "p.pdf"
            pdf.write_bytes(b"%PDF-1.4\n")
            err = io.StringIO()
            with patch.object(import_arxiv.shutil, "which", return_value=None), \
                 patch.dict(sys.modules, {"fitz": None}), \
                 patch.object(sys, "stderr", err):
                pages = import_arxiv.pdf_pages(pdf)
            self.assertEqual(pages, [])
            self.assertIn("poppler-utils", err.getvalue())
            self.assertIn("python3-fitz", err.getvalue())


if __name__ == "__main__":
    unittest.main()
