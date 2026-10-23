# Publication and submission status

The code and exact evidence are published in the official upstream contribution:
https://github.com/WolframInstitute/Rule30PrizeKit/pull/1

The complete modular theorem excludes all tails of length at most six at padding
74. The standalone essay carries the sixteen new six-bit black-ended cores only.
Both kit versions pass the modular checks. Both essays' exact embedded Lean source,
including the root import, passes the pinned kit's unchanged checker. Tests confirm
that the essays embed those checked bytes. Public remote Wolfram SAT computations
independently confirm the basic finite obstructions.

There is **no evaluated Wolfram/LeanLink notebook, prize API submission, submission
ID, or prize-verifier verdict**. Public code availability is not maintainer
acceptance or prize registration.

Remaining steps:

1. With permission, install and activate a local Wolfram Engine 14.3+ if needed.
   The installation question is pending. Account activation is performed by the
   human; passwords and license keys must not be put in chat or the repository.
2. Evaluate the official `HowToStart.md` starter essay in that kernel, following
   https://www.wolframcloud.com/obj/rule-30-prize/Agents/skill.md .
3. In a fresh kernel with Lean 4.35.0 on PATH, set `RULE30PRIZE_KIT` to the prepared
   pinned worktree and `RULE30_NOTEBOOK_CONFIG` to this folder's
   `notebook-config.json`; evaluate `../forbidden-suffix/build-notebook.wl` as UTF-8.
   It requires actual LeanLink kernel checks of the preflight and the notebook's
   own environment before emitting a verification report. It never submits.
4. Inspect the built notebook and its verification report. Obtain the human author
   name and explicit submission consent. These are separate from GitHub permission.
5. Connect the human's Wolfram ID locally, submit the built notebook with the
   official PR as its repository, and report the returned ID and status-page URL.
   Inspect the eventual automatic-verifier result; do not assume success from the
   local checks.

The original downloaded essay is preserved. Research artifacts and reproducible
scripts are in this checkout and the linked PR; no ongoing background research
job is required for these results.
