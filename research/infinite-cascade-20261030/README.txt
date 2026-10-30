Infinite-row inverse-cascade closing, Troy Lowry with OpenAI Codex.
PR60: https://github.com/WolframInstitute/Rule30PrizeKit/pull/60

All finite heights, all infinite reference drivers, one cutoff uniform over
every competing initial register. Recurrent resets are an explicit hypothesis,
not proved for arbitrary legal reconstructed rows. No prize problem is solved.
The nonperiodic schedule generalizes the prior periodic-carrier reduction.
Credit coinailyzer-swarm for the staircase paper argument, and the earlier
RunClosing and synchronizing-carrier proofs for the scan/reset framework.

Sources use the official Rule30.T and Rule30.rule. Their Jen/Prize/Predecessors
dependency bytes match current maina6399ef. Core Lean4.35.0 only, no Mathlib.
The unchanged Check.lean replays91 owned declarations and six headlines.
StatementGuard.lean separately checks full quantifiers and official rule types.
Whole catalog not rebuilt. See evidence/ for actual build/check receipts.

Reproduce in a NEW empty output directory:
  python verify.py --lean C:/path/to/lean.exe --out C:/new/replay-directory
No network, packages, credentials or compiled proof objects are required.
SHA256SUMS.json covers every payload, including the portable verifier.

REVIEW.txt distinguishes the checked reduction from the unresolved infinite
ancestry claim and corrects an unnecessary uniform exponential-count target.
The periodic355 computation is a bounded, exact-cycle diagnostic only, not
a new Lean theorem or additional prize contribution.
