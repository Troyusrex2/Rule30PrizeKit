# Publication and submission status

The code and exact evidence are published in the official upstream contribution:
https://github.com/WolframInstitute/Rule30PrizeKit/pull/1

The complete modular theorem excludes all tails of length at most six at padding
74. The standalone essay carries the sixteen new six-bit black-ended cores only.
Both kit versions pass the modular checks. Both essays' exact embedded Lean source,
including the root import, passes the pinned kit's unchanged checker. Tests confirm
that the essays embed those checked bytes. Public remote Wolfram SAT computations
independently confirm the basic finite obstructions.

Both research notebooks are now built and evaluated in Wolfram Engine 15.0.0.
Their own LeanLink module replays pass: 252 declarations for the suffix families
and 939 for the sixteen six-bit cores. Both saved notebooks preserve the exact
checked source and contain successful kernel-check output with zero message cells.
The valid starter and its negative controls pass in four fresh processes. The
local MCP evaluator and `ReadNotebook` work. Engine activation and cloud sign-in
are complete; no further terminal sign-in is currently needed.

There is **no prize API submission, submission ID, or prize-verifier verdict**.
Local checks and public code availability are not maintainer acceptance or prize
registration. See `../windows-notebook/README.md` for the Windows runtime workaround.

Remaining steps:

1. Obtain the human author name and explicit submission consent for the built
   notebooks. These are separate from GitHub permission. The agent workflow says
   to "get their explicit go-ahead and their name for authors":
   https://www.wolframcloud.com/obj/rule-30-prize/Agents/skill.md .
2. Fill the human author byline, preserving and checking the evaluated input cells.
3. Submit the built notebooks with the official PR as their repository, and report
   each returned ID and status-page URL.
   Inspect the eventual automatic-verifier result; do not assume success from the
   local checks.

The original downloaded essay is preserved. Research artifacts and reproducible
scripts are in this checkout and the linked PR; no ongoing background research
job is required for these results.
