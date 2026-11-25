# How to use this atlas

## How do I start?

Install the build-proof-atlas skill in your coding agent, or point it to the downloaded SKILL.md. Give it a paper edition and choose one theorem or the whole paper. For example: “Build a proof atlas for this paper. Formalize all stated results, keep conjectures separate, and ask me where to host it.” The agent checks the edition, creates the explorer and dashboard, and finds or installs the pinned Lean tools.

## Where should I look first?

Open the explorer to read a theorem in plain English, see the original paper passage, follow a structured proof when available, or inspect the Lean source. The dependency graph can follow a selected chain or show the entire paper. Open the dashboard to see the authorized scope, current claim, checked subproofs, remaining obligations, and evidence.

## What has actually been verified?

Lean checked means Lean accepted the recorded formal declaration against its expected type. Machine verified on GitHub means a separate run checked it for the published revision; the badge links to evidence. The automated correspondence comparison is an assessment by the proof agent. Author reviewed the theorem statement proved in Lean means a named person explicitly accepted the displayed comparison. The exact material and review date are available in review history. The Plain English and Lamport proof views are explanations, not machine-checked, and Lean’s proof may take a different route from the paper’s. The checks catch mistakes, not proof files written to fool them; for proofs you do not trust, use a dedicated checker such as Comparator.

## How do I open author review?

Say “Open the local review dashboard for this paper.” You can ask during proof generation or after returning to the project later. The agent starts or reopens the local browser server. Open any claim from the queue. For a direct launch, run `python <skill>/scripts/atlas.py review <project-folder>`. To share a terminal session without opening a browser automatically, add `--no-open`. The terminal alternative is `python <skill>/scripts/atlas.py approve <project-folder> --by "Your name"`. Add a claim label before --by to select just that theorem.

## Why does the review flag some Lean operations?

Lean assigns values to operations such as division by zero. A flag tells you where a definition uses such an operation. In each new comparison, the agent records a status and a short explanation for every finding in the current scan.

Start with “needs attention.” For example, if a rate is defined by taking an infimum, the review might ask, “What guarantees that the set in `constrainedRate` is nonempty and bounded below?” If you know the relevant lemma or intended convention, you can identify it in your feedback. The agent can save the comparison with the question open, and the theorem keeps its Lean proof status.

Open “Show explained uses” to see the findings marked “justified.” Each explanation names the hypothesis, lemma, or intended convention that accounts for the operation. The Lean view shows the full scan. When an older comparison says “not assessed,” you can ask, “Update this claim’s comparison and explain its flagged operations.” For an atlas whose audit predates the scan itself, ask the agent to refresh the audit first.

## How much work goes into finding examples?

A witness is a Lean-checked example where a theorem’s hypotheses hold together. For example, if a conclusion applies at a point where a function is differentiable, the witness supplies such a point. You can inspect the example and the proposition it proves in the Lean view or on the claim’s review page.

There is no setup question. By default the agent tries a concrete example or an existing lemma. If a new mathematical result is needed, it records the missing statement with the claim and continues with independent work. A theorem can still be marked “Lean checked” while its dashboard row says “No checked example shows the hypotheses can hold.”

To change the effort for the whole paper, say “Skip witness searches for this paper” or “Pursue witnesses even when they need new lemmas.” To make one exception, say “Do the extra work for Theorem 8.” To undo that exception, say “Use the paper’s usual witness policy for Theorem 8 again.” The atlas saves your preference across sessions. Earlier checked examples remain available and are checked again when their claims are re-audited.

## What if my intent is unclear before proof work begins?

The agent compares the paper passage with the proposed Lean statement before starting the proof. Your approval is optional. If the two readings differ in a way that needs your judgment, the agent shows them side by side and asks a specific question, such as “Does the identity include the endpoint?”

Choose “Work through this now” to settle the interpretation together, or “Save the question and continue with independent claims” to return to it later. When you are away, the agent uses the second option. The question stays in the review queue. The affected claim and any claims that depend on the answer wait. The agent revisits outstanding questions before its final summary.

During proof work, the queue can show “Statement drafted (proof in progress)” or “Statement approved (proof in progress).” If you approve the statement at this stage, that approval carries over when the proof closes against the same statement and comparison. A change to the formal statement calls for a fresh comparison.

## What am I being asked to decide?

In “How the statements compare,” each row explains how the formal theorem relates to one case or numbered clause in the paper. For a classified comparison, the dashboard’s difference count links to the cases in the Paper view. For example, “other form” can mean the same bound uses a different index, “restriction” means the Lean statement covers a narrower domain, and “weaker conclusion” means Lean proves a coarser bound, omits a conclusion clause, or leaves an algorithmic, runtime, or explicitness claim unproved. A “weaker conclusion” cannot be marked as a match: the missing obligation stays tracked as an open subproof and leaves the parent claim open (“Subproofs checked”) until proved. Older comparisons say “not classified” until their cases are labeled.

The review page and Lean view also show three statement metadata checks: the declaration’s axiom profile (constructive with zero axioms versus standard classical axioms), any `noncomputable` definitions referenced by the statement (so you can spot when an “explicit” or algorithmic claim relies on noncomputable choice), any non-Mathlib third-party external repositories in `lake-manifest.json`, and an expandable notation-free Lean signature (`pp.notation false`) beside each definition’s source code.

Read “Scope of the conclusion” and “Agent recommendation” before deciding. When an assumption or endpoint is in doubt, the agent supplies wording you can use or edit when reporting the difference. Only your explicit decision records an author review.

Read the paper passage and the mathematical interpretation under What Lean proved. Compare the objects, assumptions, ranges, and conclusions. Expand a definition or open the paper PDF and exact Lean evidence if helpful. Select Yes, these match to approve. Select I see a difference and describe it in your own words to flag a discrepancy or ask a question. Skip for now leaves the decision open. An author may review as many or as few claims as they wish.

## What if the two sides differ?

If a display says “all dimensions” but the formal declaration says “dimension at least two,” the agent corrects the display and compares again. If the paper actually claims all dimensions, the agent investigates dimension one. It may prove that case, combine the cases, and return with the corrected theorem. If the agent finds a counterexample instead, it shows the counterexample and asks the author how to address it. Only the author decides whether to revise the paper.

A verified upper bound stays available if the paper also needs a lower bound. The missing lower bound becomes an open paper obligation. When Lean proves a stronger result, the agent can derive the paper’s exact theorem. When interpretations are ambiguous, the agent presents the alternatives and their mathematical consequences. A reported discrepancy reopens correspondence while retaining the formal evidence. An active agent checks the review queue at checkpoints. If your agent session has ended, say “Resume this atlas and resolve the reported differences.” The browser saves feedback even when no agent is running.

## Where do suggested paper changes go?

An optional **Lean proves more** note identifies extra results that come with the proof. You can accept coverage of the paper and add your own wording in **Scope note to display with my approval**. That note accompanies your current approval in the explorer. A scope note explains what was checked. Use **Suggested manuscript edit** when you want a change tracked for the paper.

Open **Manuscript edits** from the review dashboard. The optional manuscript-edit field on each review sends wording suggestions to this list, including suggestions saved alongside an approval. The agent also checks ordinary review comments for editorial requests when it resumes. A proposed edit quotes the current passage, provides a replacement and links to its claim.

To make the change yourself, copy the proposed replacement. On the local edits page select the suggestions you handled and choose **Clear selected**, or use **Clear all active suggestions**. **Restore selected** brings cleared items back. Clearing is a housekeeping decision and does not certify that a manuscript was revised.

To delegate the edit, select it and choose **Request draft for selected**. An active agent prepares a reviewable change in the editable manuscript and records the draft location. To resume a stopped session, say “Prepare the requested manuscript edits.” Review the diff before authorizing integration. The agent records the applied revision and refreshes affected comparisons when the new paper edition is pinned. Approving a theorem, requesting a draft, and publishing a revised manuscript are separate decisions.

## What happens to my decision?

The local project records your supplied name, time, decision, and the comparison you saw. Your name is self-reported. Adding the first analysis to previously approved, identical readings preserves that approval and labels it as predating the analysis. The local dashboard saves decisions before publication. Ask the agent to publish the committed review records to the paper’s authorized destination when ready. Hosted GitHub Pages displays that revision’s history; open your local project to submit a new decision. A coauthor working in another checkout should sync and reconcile review records before publishing.

A changed formal statement, relevant project definition, toolchain pin, paper source, or displayed reading calls for a fresh comparison or review. A proof-only edit can keep approval after Lean rechecks the same statement. An old browser tab asks you to reload when the evidence or decisions have changed. Historical decisions remain available.

## Why is a claim waiting?

“Proof agent” names the owner of the next action. An active, authorized coding session investigates the finding, integrates a successful repair, rechecks the release declaration and follows it to the agreed destination. You do not need to resubmit the same question or approve a scratch result. If the session is closed, its saved tasks are picked up when you resume. The agent reports a specific blocker or author decision when one is needed. The dashboard and linked GitHub run show actual verification activity.

The queue gives the next actor and action. Proof work can proceed with review skipped. Older atlases keep their machine evidence and counts. To enable optional review for an old claim, ask the agent to refresh its audit with the current skill and prepare the two independent readings. If you only want to read the atlas, no migration is needed.
