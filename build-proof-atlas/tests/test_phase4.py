from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import atlas
import author_review as review
import manuscript_edits as edits


class Phase4ManifestAndBacklog(unittest.TestCase):
    def _build_fixture(self, root, *, profile="quick"):
        def source(name, data):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            return {"path": name, "sha256": hashlib.sha256(data).hexdigest()}

        tex = source("paper.tex", (
            r"\begin{lemma}\label{lem:helper}Helper_bound with 100\% rate.\end{lemma}" "\n"
            r"\begin{theorem}\label{thm:main}Main convergence theorem.\end{theorem}" "\n"
            r"\begin{corollary}\label{cor:fast}Conditional speedup corollary.\end{corollary}" "\n"
            r"\begin{proposition}\label{prop:alg}Explicit algorithmic bound.\end{proposition}" "\n"
            r"\begin{remark}\label{rem:promoted}Promoted headline remark.\end{remark}" "\n"
            r"\begin{proposition}\label{prop:demoted}Demoted supporting prop.\end{proposition}" "\n"
            r"\begin{example}\label{ex:demo}Concrete example.\end{example}" "\n"
            r"\begin{conjecture}\label{conj:open}Open dispersion conjecture.\end{conjecture}" "\n"
        ).encode("utf-8"))
        pdf = source("paper.pdf", b"%PDF-1.4\n")

        source("lean/lean-toolchain", b"leanprover/lean4:v4.24.0\n")
        source("lean/lake-manifest.json", json.dumps({
            "version": "1.1.0",
            "packagesDir": ".lake/packages",
            "packages": [
                {"name": "mathlib", "type": "git", "url": "https://github.com/leanprover-community/mathlib4",
                 "rev": "1234567890abcdef1234567890abcdef12345678", "inherited": False},
                {"name": "custom_opt", "type": "git", "url": "https://github.com/example/custom_opt",
                 "rev": "fedcba0987654321fedcba0987654321fedcba09", "inherited": False},
            ],
        }).encode("utf-8"))
        stmt_file = source(
            "lean/Statements/All.lean",
            b"def Helper : Prop := True\n"
            b"def Main : Prop := True\n"
            b"def Fast : Prop := True\n"
            b"def Alg : Prop := True\n"
            b"def Promoted : Prop := True\n",
        )
        proof_main = source("lean/Proofs/Main.lean", b"import Statements.All\ntheorem main : Main := trivial\n")
        proof_fast = source("lean/Proofs/Fast.lean", b"import Statements.All\ntheorem fast (_ : Helper) : Fast := trivial\n")
        proof_alg = source("lean/Proofs/Alg.lean", b"import Statements.All\ntheorem part1 : True := trivial\n")
        proof_prom = source("lean/Proofs/Prom.lean", b"import Statements.All\ntheorem prom : Promoted := trivial\n")
        ex_file = source("lean/Examples/Main.lean", b"import Statements.All\ntheorem main_wit : True := trivial\n")
        source("run.log", b"Lean build OK\n")

        def make_stmt(expected, line, *, noncomp=False):
            sha = hashlib.sha256(expected.encode()).hexdigest()
            const = {"name": expected, "file": "Statements/All.lean", "lines": [line, line], "sha256": sha}
            if noncomp:
                const["noncomputable"] = True
            return {
                "expected": expected,
                "sha256": hashlib.sha256(f"{expected} {sha}\n".encode()).hexdigest(),
                "constants": [const],
            }

        ext_pkgs = [
            {"name": "mathlib", "rev": "1234567890abcdef1234567890abcdef12345678",
             "url": "https://github.com/leanprover-community/mathlib4", "direct": True, "third_party": False},
            {"name": "custom_opt", "rev": "fedcba0987654321fedcba0987654321fedcba09",
             "url": "https://github.com/example/custom_opt", "direct": True, "third_party": True},
        ]

        # 1. lem:helper — Gate 1 statement_only, unresolved default + chosen reading needing confirmation + deferred bridging
        helper_audit = {
            "statement_only": True, "expected": "Statements.Helper", "axioms": [],
            "axiom_profile": "Constructive (0 axioms)",
            "toolchain": "leanprover/lean4:v4.24.0",
            "statements": ["Statements"],
            "external_packages": ext_pkgs,
            "checked_inputs": {"Statements/All.lean": stmt_file["sha256"]},
            "statement": make_stmt("Statements.Helper", 1),
            "defaults": [
                {"constant": "Statements.Helper", "file": "Statements/All.lean", "lines": [1, 1],
                 "construct": "ENNReal.toReal"},
                {"constant": "Statements.Helper", "file": "Statements/All.lean", "lines": [1, 1],
                 "construct": "Real.log"},
            ],
        }
        source("evidence/helper-stmt.json", json.dumps(helper_audit).encode())

        # 2. thm:main — Unconditionally closed, with witness, distilled=True, CI-verified, author-reviewed
        main_audit = {
            "expected": "Statements.Main", "declaration": "Proofs.Main.main",
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
            "axiom_profile": "Standard classical axioms (Classical.choice, Quot.sound, propext)",
            "toolchain": "leanprover/lean4:v4.24.0",
            "statements": ["Statements"],
            "external_packages": ext_pkgs,
            "checked_inputs": {
                "Statements/All.lean": stmt_file["sha256"],
                "Proofs/Main.lean": proof_main["sha256"],
                "Examples/Main.lean": ex_file["sha256"],
            },
            "statement": make_stmt("Statements.Main", 2),
            "hypotheses": {
                "declaration": "Examples.Main.main_wit", "proposition": "True",
                "file": "Examples/Main.lean", "lines": [2, 2], "axioms": [],
            },
            "defaults": [],
        }
        main_audit_info = source("evidence/main.json", json.dumps(main_audit).encode())

        # 3. cor:fast — Conditional assuming lem:helper, no witness, undistilled in quick mode
        fast_audit = {
            "expected": "Statements.Fast", "declaration": "Proofs.Fast.fast",
            "assumes": ["Statements.Helper"],
            "axioms": [], "axiom_profile": "Constructive (0 axioms)",
            "toolchain": "leanprover/lean4:v4.24.0",
            "statements": ["Statements"],
            "external_packages": ext_pkgs,
            "checked_inputs": {
                "Statements/All.lean": stmt_file["sha256"],
                "Proofs/Fast.lean": proof_fast["sha256"],
            },
            "statement": make_stmt("Statements.Fast", 3),
            "defaults": [],
        }
        source("evidence/fast.json", json.dumps(fast_audit).encode())

        # 4. prop:alg — Subproofs checked, statement_check with noncomputable + weaker conclusion
        alg_audit = {
            "statement_only": True, "expected": "Statements.Alg", "axioms": [],
            "axiom_profile": "Constructive (0 axioms)",
            "toolchain": "leanprover/lean4:v4.24.0",
            "statements": ["Statements"],
            "external_packages": ext_pkgs,
            "checked_inputs": {"Statements/All.lean": stmt_file["sha256"]},
            "statement": make_stmt("Statements.Alg", 4, noncomp=True),
            "defaults": [],
        }
        source("evidence/alg-stmt.json", json.dumps(alg_audit).encode())

        # 5. rem:promoted — Promoted to headline via reader.json headline=True, closed, no witness, undistilled
        prom_audit = {
            "expected": "Statements.Promoted", "declaration": "Proofs.Prom.prom",
            "axioms": [], "axiom_profile": "Constructive (0 axioms)",
            "toolchain": "leanprover/lean4:v4.24.0",
            "statements": ["Statements"],
            "external_packages": ext_pkgs,
            "checked_inputs": {
                "Statements/All.lean": stmt_file["sha256"],
                "Proofs/Prom.lean": proof_prom["sha256"],
            },
            "statement": make_stmt("Statements.Promoted", 5),
            "defaults": [],
        }
        source("evidence/prom.json", json.dumps(prom_audit).encode())

        reader = {
            "schema_version": 1,
            "claims": {
                "lem:helper": {"reference": "Lemma 1"},
                "thm:main": {"reference": "Theorem 2"},
                "cor:fast": {"reference": "Corollary 3"},
                "prop:alg": {"reference": "Proposition 4"},
                "rem:promoted": {"reference": "Remark 5", "headline": True},
                "prop:demoted": {"reference": "Proposition 6", "headline": False},
                "ex:demo": {"reference": "Example 7"},
                "conj:open": {"reference": "Conjecture 8"},
            },
            "dependencies": [
                {"claim": "cor:fast", "prerequisite": "lem:helper", "reason": "Uses helper bound"},
            ],
        }
        (root / "reader.json").write_text(json.dumps(reader), encoding="utf-8")

        project = {
            "schema_version": 1,
            "environments": ["lemma", "theorem", "corollary", "proposition", "remark", "example", "conjecture"],
            "edition": "arXiv:2611.99999v1",
            "title": "Rate & Bound Analysis",
            "authors": ["Alice Author", "Bob Coauthor"],
            "tex": [tex],
            "pdf": pdf,
            "reader": "reader.json",
            "proof_work": {"mode": "paper", "profile": profile},
            "hosting": {
                "decision": "github",
                "repository": "https://github.com/example/rate-atlas",
                "site": "https://example.github.io/rate-atlas/",
                "visibility": "public",
                "lean_ci": "enabled",
            },
            "work": {
                "lem:helper": {
                    "status": "drafted",
                    "scope": "Helper lemma.",
                    "updated": "2026-11-26T00:00:00Z",
                    "statement_check": {"audit": "evidence/helper-stmt.json", "package": "lean", "expected": "Statements.Helper"},
                    "deferred_bridging_lemmas": ["Bridge custom helper rate to Mathlib iInf"],
                },
                "thm:main": {
                    "status": "closed",
                    "scope": "Main theorem.",
                    "run_log": "run.log",
                    "distilled": True,
                    "updated": "2026-11-26T00:00:00Z",
                    "checked_inputs": {
                        "lean/Statements/All.lean": stmt_file["sha256"],
                        "lean/Proofs/Main.lean": proof_main["sha256"],
                        "lean/Examples/Main.lean": ex_file["sha256"],
                    },
                    "closure": {
                        "package": "lean", "expected": "Statements.Main",
                        "declaration": "Proofs.Main.main", "audit": "evidence/main.json",
                        "correspondence": "Matches Theorem 2.",
                    },
                },
                "cor:fast": {
                    "status": "conditional",
                    "scope": "Conditional corollary.",
                    "run_log": "run.log",
                    "assumes": ["lem:helper"],
                    "updated": "2026-11-26T00:00:00Z",
                    "checked_inputs": {
                        "lean/Statements/All.lean": stmt_file["sha256"],
                        "lean/Proofs/Fast.lean": proof_fast["sha256"],
                    },
                    "closure": {
                        "package": "lean", "expected": "Statements.Fast",
                        "declaration": "Proofs.Fast.fast", "audit": "evidence/fast.json",
                        "correspondence": "Matches Corollary 3 assuming Lemma 1.",
                    },
                },
                "prop:alg": {
                    "status": "attempted",
                    "scope": "Algebraic bound checked; runtime bound open.",
                    "run_log": "run.log",
                    "updated": "2026-11-26T00:00:00Z",
                    "checked_inputs": {"lean/Proofs/Alg.lean": proof_alg["sha256"]},
                    "statement_check": {"audit": "evidence/alg-stmt.json", "package": "lean", "expected": "Statements.Alg"},
                    "subproofs": [
                        {"title": "Existence bound", "status": "checked", "declaration": "Proofs.Alg.part1"},
                        {"title": "O(n log n) runtime bound", "status": "open"},
                    ],
                },
                "rem:promoted": {
                    "status": "closed",
                    "scope": "Promoted headline remark.",
                    "run_log": "run.log",
                    "witness_missing_result": "Need non-degenerate positive-variance construction",
                    "updated": "2026-11-26T00:00:00Z",
                    "checked_inputs": {
                        "lean/Statements/All.lean": stmt_file["sha256"],
                        "lean/Proofs/Prom.lean": proof_prom["sha256"],
                    },
                    "closure": {
                        "package": "lean", "expected": "Statements.Promoted",
                        "declaration": "Proofs.Prom.prom", "audit": "evidence/prom.json",
                        "correspondence": "Matches Remark 5.",
                    },
                },
            },
        }
        (root / "project.json").write_text(json.dumps(project, indent=2), encoding="utf-8")

        # Record comparisons:
        # lem:helper -> chosen reading with needs_author_confirmation, 1 justified + 1 needs attention default
        pkt_h = review.get_packet(root, "lem:helper")
        by_construct = {d["construct"]: d["id"] for d in pkt_h["defaults"]}
        review.save_comparison(root, "lem:helper", {
            "bindings": pkt_h["view"]["bindings"],
            "result": "match",
            "needs_author_confirmation": True,
            "paper_reading": "Helper bound holds at endpoint.",
            "lean_reading": "Statements.Helper fixes strict interior endpoint.",
            "paper_refs": "paper.tex, lem:helper",
            "lean_refs": "Statements.Helper",
            "analysis": {
                "summary": "Unattended reading fixes strict endpoint.",
                "scope": "Interior interval only.",
                "cases": [{
                    "case": "C1 (Endpoint)",
                    "paper": "Unspecified endpoint",
                    "lean": "Strict inequality x > 0",
                    "why": "Best-supported reading in quick mode.",
                    "kind": "chosen reading",
                    "needs_author_confirmation": True,
                }],
                "default_assessments": {
                    by_construct["ENNReal.toReal"]: {
                        "status": "needs attention",
                        "explanation": "What guarantees the expectation is finite (not top)?",
                    },
                    by_construct["Real.log"]: {
                        "status": "justified",
                        "explanation": "Hypothesis x > 0 prevents log 0.",
                    },
                },
                "advice": "Confirm whether x > 0 is intended.",
            },
        })

        # thm:main -> match with restriction note, approved by author with scope note
        pkt_m = review.get_packet(root, "thm:main")
        review.save_comparison(root, "thm:main", {
            "bindings": pkt_m["view"]["bindings"],
            "result": "match",
            "paper_reading": "Main convergence theorem holds.",
            "lean_reading": "Statements.Main holds for finite alphabets.",
            "paper_refs": "paper.tex, thm:main",
            "lean_refs": "Statements.Main",
            "analysis": {
                "summary": "Matches paper on finite alphabets.",
                "scope": "Finite alphabet restriction.",
                "cases": [
                    {"case": "C1", "paper": "Convergence", "lean": "Statements.Main", "why": "Direct.", "kind": "agrees"},
                    {"case": "C2", "paper": "General alphabet", "lean": "Finite alphabet", "why": "Restricted to Fintype.", "kind": "restriction"},
                ],
                "advice": "Approve if finite-alphabet scope is acceptable.",
            },
        })
        pkt_m = review.get_packet(root, "thm:main")
        review.decide(root, "thm:main", pkt_m["token"], "approve", "Alice Author",
                      scope_note="Finite alphabet matches Section 2.")

        # prop:alg -> difference with weaker conclusion (runtime omitted)
        pkt_a = review.get_packet(root, "prop:alg")
        review.save_comparison(root, "prop:alg", {
            "bindings": pkt_a["view"]["bindings"],
            "result": "difference",
            "issue": "Runtime complexity bound not formalized; construction is noncomputable.",
            "actor": "Proof agent",
            "next": "Prove the O(n log n) runtime subproof or scope the manuscript claim.",
            "paper_reading": "Explicit O(n log n) algorithm achieves bound.",
            "lean_reading": "Noncomputable existence of bound only.",
            "paper_refs": "paper.tex, prop:alg",
            "lean_refs": "Statements.Alg",
            "analysis": {
                "summary": "Existence only; runtime and computability omitted.",
                "scope": "Mathematical existence only.",
                "cases": [{
                    "case": "C1 (Algorithmic runtime)",
                    "paper": "Explicit O(n log n) algorithm",
                    "lean": "Noncomputable existence",
                    "why": "Complexity and computability are outside current Lean statement.",
                    "kind": "weaker conclusion",
                }],
                "advice": "Keep Proposition 4 open until runtime is proved or scoped.",
                "suggested_feedback": "Clarify that Lean checks mathematical existence only.",
            },
        })

        # CI receipt verifying thm:main
        commit = "c" * 40
        ci_data = {
            "repository": "example/rate-atlas",
            "commit": commit,
            "run_id": 777,
            "attempt": 1,
            "claims": {
                "thm:main": {
                    "expected": "Statements.Main",
                    "declaration": "Proofs.Main.main",
                    "toolchain": "leanprover/lean4:v4.24.0",
                    "axioms": ["propext", "Classical.choice", "Quot.sound"],
                    "audit_sha256": main_audit_info["sha256"],
                    "statement_sha256": main_audit["statement"]["sha256"],
                    "hypotheses": "True",
                }
            },
        }
        ci_path = root / "ci.json"
        ci_path.write_text(json.dumps(ci_data), encoding="utf-8")
        return ci_path, commit

    def test_headline_supporting_counts_backlog_and_ui(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder).resolve()
            ci_path, commit = self._build_fixture(root, profile="quick")

            with redirect_stdout(io.StringIO()):
                atlas.build(root, ci_receipt=ci_path, commit=commit)

            rw = atlas.review_work(root, ci_receipt=ci_path)
            summary = rw["summary"]

            # Headline: thm:main (closed), cor:fast (conditional), prop:alg (subproofs_checked), rem:promoted (closed)
            h = summary["headline"]
            self.assertEqual(h["total"], 4)
            self.assertEqual(h["unconditionally_closed"], 2)
            self.assertEqual(h["conditional"], 1)
            self.assertEqual(h["subproofs_checked"], 1)
            self.assertEqual(h["open"], 0)
            self.assertEqual(h["with_witness"], 1)
            self.assertEqual(h["needs_confirmation"], 1)  # cor:fast via lem:helper
            self.assertEqual(h["needs_confirmation_direct"], 0)
            self.assertEqual(h["machine_verified"], 1)
            self.assertEqual(h["author_reviewed"], 1)

            # Supporting: lem:helper (open), prop:demoted (open), ex:demo (open)
            s = summary["supporting"]
            self.assertEqual(s["total"], 3)
            self.assertEqual(s["unconditionally_closed"], 0)
            self.assertEqual(s["open"], 3)
            self.assertEqual(s["needs_confirmation"], 1)
            self.assertEqual(s["needs_confirmation_direct"], 1)

            # All stated results (excludes conjecture)
            a = summary["all_results"]
            self.assertEqual(a["total"], 7)
            self.assertEqual(a["unconditionally_closed"], 2)
            self.assertEqual(a["conditional"], 1)
            self.assertEqual(a["subproofs_checked"], 1)
            self.assertEqual(a["open"], 3)

            # Conjectures tracked separately
            conj = summary["conjectures"]
            self.assertEqual(conj["total"], 1)
            self.assertEqual(conj["open"], 1)

            # Verify prioritized Refinement Backlog (P1..P5)
            backlog = rw["refinement_backlog"]
            by_prio = {g["priority"]: g for g in backlog["priorities"]}
            self.assertEqual([g["priority"] for g in backlog["priorities"]], [1, 2, 3, 4, 5])
            # P1: lem:helper needs author confirmation, with dependent cor:fast
            self.assertEqual([i["claim"] for i in by_prio[1]["items"]], ["lem:helper"])
            self.assertEqual([d["id"] for d in by_prio[1]["items"][0]["dependents"]], ["cor:fast"])
            # P2: cor:fast conditional assuming lem:helper
            self.assertEqual([i["claim"] for i in by_prio[2]["items"]], ["cor:fast"])
            self.assertEqual(by_prio[2]["items"][0]["assumes"][0]["id"], "lem:helper")
            # P3: prop:alg has weaker conclusion + noncomputable + open subproof
            self.assertEqual([i["claim"] for i in by_prio[3]["items"]], ["prop:alg"])
            self.assertEqual(by_prio[3]["items"][0]["noncomputable_constants"], ["Statements.Alg"])
            self.assertEqual(by_prio[3]["items"][0]["open_subproofs"], ["O(n log n) runtime bound"])
            # P4: missing witnesses (lem:helper, cor:fast, prop:alg, rem:promoted) & unresolved default (only ENNReal.toReal on lem:helper, NOT justified Real.log!)
            p4_by_claim = {i["claim"]: i for i in by_prio[4]["items"]}
            self.assertEqual(set(p4_by_claim), {"lem:helper", "cor:fast", "prop:alg", "rem:promoted"})
            self.assertNotIn("thm:main", p4_by_claim)
            self.assertEqual([d["construct"] for d in p4_by_claim["lem:helper"]["unresolved_defaults"]], ["ENNReal.toReal"])
            # P5: lem:helper has deferred bridging lemma; cor:fast and rem:promoted are undistilled in quick mode (thm:main has distilled=True!)
            p5_by_claim = {i["claim"]: i for i in by_prio[5]["items"]}
            self.assertEqual(set(p5_by_claim), {"lem:helper", "cor:fast", "rem:promoted"})
            self.assertEqual(p5_by_claim["lem:helper"]["deferred_bridging_lemmas"], ["Bridge custom helper rate to Mathlib iInf"])
            self.assertTrue(p5_by_claim["cor:fast"]["undistilled"])
            self.assertTrue(p5_by_claim["rem:promoted"]["undistilled"])
            self.assertNotIn("thm:main", p5_by_claim)

            # Verify progress.html and explorer home/reader HTML
            progress_html = (root / "dist/progress.html").read_text(encoding="utf-8")
            self.assertIn("Headline results", progress_html)
            self.assertIn("Supporting results", progress_html)
            self.assertIn("Conjectures (separate)", progress_html)
            self.assertIn("Open Shortcomings &amp; Refinement Backlog", progress_html)
            self.assertIn("P1 · Needs author confirmation", progress_html)
            self.assertIn("P2 · Conditional claims waiting on unproved prerequisites", progress_html)
            self.assertIn("P3 · Open weaker-conclusion and noncomputable obligations", progress_html)
            self.assertIn("P4 · Missing hypothesis witnesses and unresolved default-value flags", progress_html)
            self.assertIn("P5 · Deferred Mathlib bridging lemmas and undistilled proofs", progress_html)
            self.assertIn("Unresolved default-value flag (1)", progress_html)
            self.assertIn("Exploratory proof (undistilled)", progress_html)
            self.assertIn('href="VERIFICATION.md"', progress_html)
            # Strict priority ordering in rendered HTML
            self.assertLess(progress_html.index('data-priority="1"'), progress_html.index('data-priority="2"'))
            self.assertLess(progress_html.index('data-priority="2"'), progress_html.index('data-priority="3"'))
            self.assertLess(progress_html.index('data-priority="3"'), progress_html.index('data-priority="4"'))
            self.assertLess(progress_html.index('data-priority="4"'), progress_html.index('data-priority="5"'))

            home_html = (root / "dist/index.html").read_text(encoding="utf-8")
            self.assertIn("Headline vs. supporting verification summary", home_html)
            self.assertIn('data-tier="headline"', home_html)
            self.assertIn('data-tier="supporting"', home_html)
            self.assertIn('data-tier="conjecture"', home_html)
            self.assertIn("Remark 5 · Headline", home_html)
            self.assertIn("Proposition 6 · Supporting", home_html)

            # Invalid non-bool headline is rejected cleanly
            bad_reader = json.loads((root / "reader.json").read_text(encoding="utf-8"))
            bad_reader["claims"]["rem:promoted"]["headline"] = "yes"
            (root / "reader.json").write_text(json.dumps(bad_reader), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "headline must be a boolean"):
                atlas.build(root)

    def test_manifest_deterministic_markdown_latex_cli_and_propose_edit(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder).resolve()
            ci_path, commit = self._build_fixture(root, profile="quick")

            first = atlas.manifest(root, ci_receipt=ci_path, commit=commit)
            second = atlas.manifest(root, ci_receipt=ci_path, commit=commit)
            # Byte-for-byte determinism
            self.assertEqual(first["markdown"], second["markdown"])
            self.assertEqual(first["latex"], second["latex"])

            md_file = root / "dist/VERIFICATION.md"
            self.assertTrue(md_file.is_file())
            self.assertEqual(md_file.read_text(encoding="utf-8"), first["markdown"])

            md = first["markdown"]
            latex = first["latex"]

            # Markdown content checks
            self.assertIn("# Formal Verification Manifest — Rate & Bound Analysis", md)
            self.assertIn("| Headline results | 4 | 2 | 1 | 1 | 0 | 1/4 | 1 | 1/4 | 1/4 |", md)
            self.assertIn("| Supporting results | 3 | 0 | 0 | 0 | 3 | 0/3 | 1 | 0/3 | 0/3 |", md)
            self.assertIn("| Conjectures (tracked separately) | 1 | 0 | 0 | 0 | 1 | 0/1 | 0 | 0/1 | 0/1 |", md)
            self.assertIn("`restriction`", md)
            self.assertIn("`chosen reading`", md)
            self.assertIn("*(Needs author confirmation)*", md)
            self.assertIn("`weaker conclusion`", md)
            self.assertIn("`Statements.Alg`", md)
            self.assertIn("`leanprover/lean4:v4.24.0`", md)
            self.assertIn("1234567890abcdef1234567890abcdef12345678", md)
            self.assertIn("`custom_opt`", md)
            self.assertIn("Standard classical axioms (Classical.choice, Quot.sound, propext)", md)
            self.assertIn("https://example.github.io/rate-atlas/", md)
            self.assertIn("https://github.com/example/rate-atlas/actions/runs/777/attempts/1", md)
            self.assertIn("```latex\n\\paragraph{Formal Verification and Scope.}", md)

            # LaTeX snippet checks (counts, caveats, deferred items, digests, URL, escaping)
            self.assertTrue(latex.startswith("\\paragraph{Formal Verification and Scope.}\n"))
            self.assertIn("2/4 headline results unconditionally closed, 1 conditional, 1 with subproofs checked", latex)
            self.assertIn("0/3 supporting results unconditionally closed, 3 open", latex)
            self.assertIn("1 conjecture tracked separately", latex)
            self.assertIn("\\texttt{quick} triage profile", latex)
            self.assertIn(f"\\texttt{{{commit[:12]}}}", latex)
            self.assertIn("restriction on C2", latex)
            self.assertIn("chosen reading on C1 (Endpoint); awaits author confirmation", latex)
            self.assertIn("weaker conclusion on C1 (Algorithmic runtime)", latex)
            self.assertIn("noncomputable: \\texttt{Statements.Alg}", latex)
            self.assertIn("conditional on Lemma 1", latex)
            self.assertIn("missing non-vacuity hypothesis witnesses", latex)
            self.assertIn("1 unresolved Lean default-value flag", latex)
            self.assertIn("deferred Mathlib bridging lemmas", latex)
            self.assertIn("undistilled exploratory proofs", latex)
            self.assertIn("Lean toolchain \\texttt{leanprover/lean4:v4.24.0}", latex)
            self.assertIn("Mathlib commit \\texttt{1234567890ab}", latex)
            self.assertIn("third-party packages \\texttt{custom\\_opt}", latex)
            self.assertIn("\\url{https://example.github.io/rate-atlas/}", latex)

            # Test CLI manifest --format latex and --propose-edit
            script = Path(__file__).resolve().parents[1] / "scripts/atlas.py"
            proc = subprocess.run(
                [sys.executable, str(script), "manifest", str(root),
                 "--ci-receipt", str(ci_path), "--commit", commit, "--format", "latex"],
                capture_output=True, text=True, check=True,
            )
            self.assertEqual(proc.stdout, latex)

            proc_edit = subprocess.run(
                [sys.executable, str(script), "manifest", str(root),
                 "--ci-receipt", str(ci_path), "--commit", commit,
                 "--propose-edit",
                 "--edit-location", "Section 1 (Introduction)",
                 "--edit-original", "All theorems in this paper are formally verified in Lean 4.",
                 "--format", "json"],
                capture_output=True, text=True, check=True,
            )
            payload = json.loads(proc_edit.stdout)
            self.assertTrue(payload["manuscript_edit"]["updated"])
            self.assertEqual(payload["manuscript_edit"]["key"], atlas.MANIFEST_EDIT_KEY)

            book, all_edits = edits.inventory(root)
            self.assertIn(atlas.MANIFEST_EDIT_KEY, all_edits)
            entry = all_edits[atlas.MANIFEST_EDIT_KEY]
            self.assertEqual(entry["location"], "Section 1 (Introduction)")
            self.assertEqual(entry["original"], "All theorems in this paper are formally verified in Lean 4.")
            self.assertEqual(entry["replacement"], latex.strip())
            self.assertEqual(entry["status"], "Proposed")

            # Requesting a draft for paper-wide scope edit is picked up by review_work and preserved by re-proposing
            edits.update(root, edits.token(book, all_edits), "request", [atlas.MANIFEST_EDIT_KEY])
            rw = atlas.review_work(root)
            self.assertTrue(any(t.get("edit") == atlas.MANIFEST_EDIT_KEY for t in rw["agent_tasks"]))

            # Re-proposing preserves Draft requested status
            _, kept, _ = edits.propose(
                root, atlas.MANIFEST_EDIT_KEY, claim="manuscript", edition="arXiv:2611.99999v1",
                replacement=latex.strip(), reason="Refresh",
            )
            self.assertEqual(kept["status"], "Draft requested")

            # Clearing the suggestion prevents silent recreation unless force=True
            book, all_edits = edits.inventory(root)
            edits.update(root, edits.token(book, all_edits), "clear", [atlas.MANIFEST_EDIT_KEY])
            _, _, recreated = edits.propose(
                root, atlas.MANIFEST_EDIT_KEY, claim="manuscript", edition="arXiv:2611.99999v1",
                replacement="Updated text", reason="Should not resurrect cleared suggestion",
            )
            self.assertFalse(recreated)

            # Rendered edits.html handles paper-wide manuscript scope edit cleanly
            edits_html = edits.render(root).decode("utf-8")
            self.assertIn("Cleared (1)", edits_html)
            self.assertIn("Section 1 (Introduction)", edits_html)

    def test_clean_thorough_project_has_empty_backlog(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder).resolve()

            def source(name, data):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
                return {"path": name, "sha256": hashlib.sha256(data).hexdigest()}

            tex = source("paper.tex", rb"\begin{theorem}\label{t}Clean result.\end{theorem}")
            pdf = source("paper.pdf", b"%PDF-1.4\n")
            stmt = source("lean/Statements/T.lean", b"def T : Prop := True\n")
            prf = source("lean/Proofs/T.lean", b"import Statements.T\ntheorem main : T := trivial\n")
            source("run.log", b"OK\n")
            t_sha = hashlib.sha256(b"Statements.T").hexdigest()
            audit = {
                "expected": "Statements.T", "declaration": "Proofs.T.main",
                "axioms": [], "axiom_profile": "Constructive (0 axioms)",
                "toolchain": "leanprover/lean4:v4.24.0", "statements": ["Statements"],
                "checked_inputs": {"Statements/T.lean": stmt["sha256"], "Proofs/T.lean": prf["sha256"]},
                "statement": {
                    "expected": "Statements.T",
                    "sha256": hashlib.sha256(f"Statements.T {t_sha}\n".encode()).hexdigest(),
                    "constants": [{"name": "Statements.T", "file": "Statements/T.lean", "lines": [1, 1], "sha256": t_sha}],
                },
                "hypotheses": {"declaration": "Examples.t_wit", "proposition": "True", "axioms": []},
                "defaults": [],
            }
            source("evidence/t.json", json.dumps(audit).encode())
            project = {
                "schema_version": 1, "environments": ["theorem"], "edition": "v1",
                "title": "Clean Paper", "tex": [tex], "pdf": pdf,
                "proof_work": {"mode": "paper", "profile": "thorough"},
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
            (root / "project.json").write_text(json.dumps(project), encoding="utf-8")
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

            with redirect_stdout(io.StringIO()):
                atlas.build(root)
            rw = atlas.review_work(root)
            self.assertEqual(rw["refinement_backlog"]["total_items"], 0)
            progress = (root / "dist/progress.html").read_text(encoding="utf-8")
            self.assertNotIn('id="refinement-backlog"', progress)

            m = atlas.manifest(root)
            self.assertIn("No non-agreeing formalization scope caveats are recorded", m["latex"])
            self.assertIn("Non-vacuity hypothesis witnesses are checked for 1/1 stated results.", m["latex"])
            self.assertIn("maintained locally", m["latex"])


if __name__ == "__main__":
    unittest.main()
