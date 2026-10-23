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

Both notebooks have been submitted as **Troy Lowry; OpenAI Codex**, with Troy's
explicit consent, through his signed-in Wolfram account. Both passed the prize
system's automated verifier and are **Lean Verified**, at pinned kit commit
`cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554`, with standard axioms only:

- Suffix families: [R30-20261023-8fe04c](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261023-8fe04c).
- Six-bit black-ended cores: [R30-20261023-524848](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261023-524848).

Those pages are accessible to the signed-in submitter and reviewers. Sanitized
verifier results are in each package's `evidence/wolfram-notebook/submission.json`.
No account identifiers or login logs are published. See
`../windows-notebook/README.md` for the Windows runtime workaround.

Remaining steps:

Human review and catalog merging remain pending. The automated verdicts certify
the formal partial results, not novelty, a full prize solution, or a prize award.

The original downloaded essay is preserved. Research artifacts and reproducible
scripts are in this checkout and the linked PR; no ongoing background research
job is required for these results.
