# Upstream catalog PR23: dyadic run-boundary sources

Troy Lowry and Codex, 25 October 2026. **Prize Problem 1 remains open.**

The checked core source theorem is now an actual upstream pull request:
[WolframInstitute/Rule30PrizeKit PR23](https://github.com/WolframInstitute/Rule30PrizeKit/pull/23).
It is open and ready for review, not merged, accepted, Human Verified or a
prize claim. No new prize essay or API submission was made.

Branch `contribution/dyadic-sources-20261025`, commit
`9b7ac6cc210b3e33cd82fb82aba8dd8454aca627`, changes exactly three files:
the new `lean/Ruliology/CellularAutomata/Rule30RunBoundarySources.lean`,
its public import and the catalog table row. The module uses core Lean only.
The exact [source](Rule30RunBoundarySources.lean), [PR body](catalog-pr-body.md),
[GitHub readback](catalog-pr23.json) and [check report](catalog-check-report.json)
are preserved here.

The theorem quantifies over every e,d,s with d<=e. At H=2^e, among the
actual sources at times s<2H-1 selected by the explicit even-depth binary
mask, exactly one is nonzero: the outer wall d=0,s=H-1. The complete
[Mathlib source bridge and deep remainder](../20261025-source-green/REPORT.md)
are separately kernel checked. The unrestricted deeper remainder can cancel
the outer contribution; there is no full noncancellation or P1 theorem.

The cold core Lake build and unchanged official checker replay passed all
56 owned constants and three headlines, with no new axioms. Those 56
constants port previously checked mathematics; they are not counted again
as 56 independent new results. The final guarded check took 9.313 seconds
and about 0.77 GiB owned RSS. The source build has no warnings; the checker
has its existing replay-deprecation warning. The verifier pin remains 3eca,
checker b882f2, and the new module is not in the reference kit until merge
and verifier-image update.

Remote branch head, exact raw source, three changed paths, ready/open state
and PR body were read back. GitHub normalized the body's line endings to
CRLF; after that explicit newline normalization the text matches exactly.
The catalog worktree is clean. No other branch or agent files were changed.
This follows the explicitly requested [Rule 30 skill's catalog workflow](https://www.wolframcloud.com/obj/rule-30-prize/Agents/skill.md).

A fresh open-PR scan also found PR22, which contributes generic Problem 2
equivalences and sufficient conditions. It was not adopted as a premise of
the P1 work; no new density or aperiodicity proof was inferred from it.
