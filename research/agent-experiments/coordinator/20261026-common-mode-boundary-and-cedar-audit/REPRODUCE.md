# Reproduce the checked statements

Use the reference kit at5473ffd075f63c9d626e63b8455805d4831b39ca and
Lean4.35.0. Keep Check.lean unchanged; SHA-256
b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905.

The cyclic diagnostic imports only the official Rule30Prize module.
Copy its source into lean/ and compile with
`lake env lean -o .lake/build/lib/lean/Rule30CyclicSubsetObstructionResearch.olean lean/Rule30CyclicSubsetObstructionResearch.lean`.
Fully replay with `lake env lean --run Check.lean Rule30CyclicSubsetObstructionResearch --claim partial`.
Its three exact headline names are in work/formal/Rule30CyclicSubsetObstructionResearch/report.json.

For Cedar, copy work/dependencies/*.lean and work/Cedar*.lean into lean/.
Compile CedarSafetySoundness, CedarSafetySemantics, CedarSafetyBridge,
CedarWhiteTransport, CedarZeroFront, CedarFiniteInjectivity, in that order.
Fully replay the final two with the same unchanged checker command and the
headlines in their report.json files. The historical private Windows runners
are retained; the source-order instructions are portable.

The complete independent clock review has its own REVIEW.md and replay
runner under work/independent-clock-review/. Its original source manifest
and all90 selected artifacts are preserved, including failed audit controls.
It refers to the preceding published clock theorem, not the cyclic diagnostic.

The finite control scripts use standard Python; SAT probes use the already
installed research Z3 package. Run writing scripts only in a fresh copy.
`python -B verify_artifacts.py` checks artifact bytes, report/source links,
unchanged checker, guards, scope and prior archives. Add --staged to check
staged bytes. This does not substitute for kernel replay.

The separate cyclic review in work/independent-cyclic-review/ includes its
own 32-artifact manifest, fresh-build replay, literal audits and guard data.
