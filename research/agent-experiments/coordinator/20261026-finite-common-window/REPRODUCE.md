# Reproduction

Use Lean4.35.0 and the official kit at5473ffd075f63c9d626e63b8455805d4831b39ca.
Check.lean must remain unchanged, with SHA256
b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905.

Copy the two work/*.lean modules into a private kit workspace. Compile
Rule30CommonPastResearch before Rule30FiniteCommonWindowResearch, using
`lake env lean -o .lake/build/lib/lean/MODULE.olean MODULE.lean` with the
actual source path substituted if placed under lean/.
Run the unchanged checker with `lake env lean --run Check.lean MODULE
--claim partial --headline MODULE.HEADLINE`. Exact headline names and full
checker JSON are under work/formal/MODULE/report.json. The two new headlines
are finite_common_window_does_not_preserve_subset and common_fails_at_three.
The private Windows runner is retained as provenance; adapt its paths.

`python -B verify_artifacts.py` audits bytes, reports, scope, guards, literal
controls and prior archives. Add --staged to audit staged bytes. It does not
substitute for replay. Run writing experiments only in a fresh copy.

Cedar's complete one-step graph and independent audit are under
work/cedar/structural/. Selected historical prefix controls and finite-cut
notes are included with their original scope. work/cedar-intake.json records
all87 checked hashes in the sealed response and the exact selected subset.
