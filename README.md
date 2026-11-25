# Proof Atlas

Proof Atlas is a skill for turning a mathematics paper into a website where readers can follow a theorem from its manuscript statement to its Lean proof and inspect the evidence that the proof checked. The explorer and progress dashboard are available from the first build and update as the formalization advances. [Explore a finished atlas](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/).

[![The Markov paper’s Folio homepage, showing its featured variance-limit theorem, a manuscript figure, and a contents list with GitHub verification badges.](docs/markov-folio.png)](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/)

## Start here

1. **Install and start.** Copy the entire [build-proof-atlas](build-proof-atlas) directory into your agent’s skills directory (for example, `~/.agents/skills/build-proof-atlas` for Codex), or give your agent the path to its SKILL.md. Try: **“Build a proof atlas for [paper and edition]. Continue through all stated results and ask me where to host it.”** To start small, name one theorem.
2. **Explore.** The agent opens a Folio explorer and dashboard. Follow a claim from the paper passage through its explanation, structured proof, and Lean source. The graph shows prerequisites; the dashboard shows progress and the next actor.
3. **Inspect evidence.** **Lean checked** identifies the formal statement that passed the local audit. **Machine verified on GitHub** links to an independent run for that revision. [See a verified claim](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/index.html#/claim/thm%3Acommon?view=lean).
4. **Review whenever you choose.** Say **“Open the local review dashboard for this paper.”** Or run `python <skill>/scripts/atlas.py review <project-folder>`. Compare the paper with **What Lean proved**, expand definitions, and select **Yes, these match**, **I see a difference**, or **Skip for now**. The CLI is also available. Proof work continues when you skip.
5. **Resolve a difference.** Describe it in ordinary language once. An active agent picks up authorized repairs, incorporates them into the checked declaration, refreshes the comparison, and verifies delivery to the agreed destination. Open findings persist across sessions. If the paper needs an author decision, the dashboard shows the evidence and the question.
6. **Share or return later.** Keep the atlas local or have the agent publish it to your chosen repository. The local project saves reviews; the published atlas shows the committed record. Open local review again to continue.

**How much work goes into examples?** A *witness* is a checked example where the theorem’s hypotheses hold together. By default the agent tries a concrete example or an existing lemma. If it needs a new lemma, it records what is missing and moves on. You can say “Skip witness searches for this paper,” “Pursue witnesses even when they need new lemmas,” or “Do the extra work for Theorem 8.” The atlas remembers your choice and keeps earlier checked examples. [Witnesses in the full author guide](build-proof-atlas/references/author-guide.md#how-much-work-goes-into-finding-examples)

**Which Lean defaults need my attention?** Open a claim’s review page and start with **needs attention**. Each item names a fact the agent still needs to establish. The agent accounts for every flagged use before saving a new comparison. Open **Show explained uses** for the justifications, or switch to the Lean view for the full scan. [Reading a flagged operation](build-proof-atlas/references/author-guide.md#why-does-the-review-flag-some-lean-operations)

**When does the agent need me?** It asks when your intended mathematical meaning affects the work, such as whether a bound includes an endpoint. During pre-proof review, the agent offers to resolve the question with you now or save it and continue independent claims. [Pre-proof review in the full author guide](build-proof-atlas/references/author-guide.md#what-if-my-intent-is-unclear-before-proof-work-begins)

![Local review example showing the paper and Lean readings above the author’s three choices.](docs/author-review.png)

Each checked claim gets a clause-by-clause analysis, the mathematical reason for agreement or disagreement (including `weaker conclusion` for omitted conjuncts or unproven algorithmic/runtime bounds, which keep a claim open), and a recommendation for the author. The review page and Lean view also surface the axiom profile (constructive vs. classical), any `noncomputable` definitions in the statement, non-Mathlib third-party dependencies, and expandable notation-free Lean signatures (`pp.notation false`), alongside precise sources and suggested feedback. Wording suggestions go in **Manuscript edits**, where authors can request a draft or clear one, several, or all handled suggestions. [Full author guide](build-proof-atlas/references/author-guide.md) · [Skill instructions](build-proof-atlas/SKILL.md).

## Try it on a real theorem

Bhaskar Krishnamachari’s *A Block Hierarchy for Rate-Distortion and Dispersion of Binary Markov Sources*, arXiv:2603.07435v4 [cs.IT], 19 November 2026, has eleven inventoried claims. Ten are proved results with GitHub verification records. The remaining claim is an open conjecture about operational dispersion. [Paper on arXiv](https://arxiv.org/abs/2603.07435v4) · [Paper-specific proof repository](https://github.com/ANRGUSC/markov-block-hierarchy-proof-atlas).

| What you want to know | Where to look |
| --- | --- |
| What does Theorem 8 establish? | Read the plain-English explanation of the variance limit, then open the original statement on page 19. [Plain English](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/index.html#/claim/thm%3Acommon?view=english) · [Paper](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/index.html#/claim/thm%3Acommon?view=paper) |
| How does the proof work? | Follow the structured Lamport proof from the one-cut estimate through the dyadic limit and the return to fixed distortion. [Lamport proof](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/index.html#/claim/thm%3Acommon?view=lamport) |
| Which other results does it use? | Follow the arrows from Lemma 7 and Corollary 9 into Theorem 8. **Selected chain** follows its prerequisites and dependents. **Whole paper** includes every claim, even those with no recorded edges. [Dependency graph](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/index.html#/graph/thm%3Acommon) |
| What did Lean actually check? | Open the formal declaration and its audit. The green badge leads to the GitHub run that rebuilt it. The public record identifies the commit, declaration, expected statement, and axioms. [Lean view](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/index.html#/claim/thm%3Acommon?view=lean) · [Verification run](https://github.com/ANRGUSC/markov-block-hierarchy-proof-atlas/actions/runs/44775699155/attempts/1) · [Verification record](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/logs/lean-verification.json) |
| How much of the paper is done? | The dashboard lists each claim, its status, the authorized scope of work, and available evidence. During formalization it can also show which claim is being written or checked. [Progress dashboard](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/progress.html) |

## What the badges mean

**Lean checked** means Lean accepted a proof of the formal statement shown in the Lean view, using only Lean’s standard axioms. **Machine verified on GitHub** means a separate GitHub run repeated that check at the published commit. **Author reviewed** means a named person compared that formal statement with the paper and accepted it. Neither Lean badge says the formal statement is the paper’s theorem. To judge that, read the Lean statement and its definitions beside the paper. The Plain English and Lamport proof views are explanations, not machine-checked, and Lean’s proof may take a different route from the paper’s.

The audit checks the declaration’s type and axioms, which catches mistakes by an honest agent. It does not defend against proof files written to game those checks. For proofs you do not trust, use a dedicated checker such as the Lean FRO’s [Comparator](https://github.com/leanprover/comparator).

## Credits

Scott Moeller and Bhaskar Krishnamachari created Proof Atlas.
