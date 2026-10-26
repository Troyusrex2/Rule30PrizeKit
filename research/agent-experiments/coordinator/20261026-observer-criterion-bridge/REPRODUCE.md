# Reproduction

Use Lean4.35.0 and pinned kit5473ffd075f63c9d626e63b8455805d4831b39ca.
The unchanged Check.lean hash is
b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905.

In a private copy, build the official Rule30TraceEdge dependency, then place
Rule30DividedDifference and Rule30CommonGauge under
lean/Ruliology/CellularAutomata/. Compile them in that order. Run
`lake env lean --run Check.lean Ruliology.CellularAutomata.MODULE --claim
partial --headline Ruliology.CellularAutomata.MODULE.HEADLINE` for the exact
headlines recorded in work/formal/MODULE/report.json. Each module report
contains the complete unchanged-checker JSON, not just an axiom audit.

The retained Windows runner records the actual private build and replay.
Its paths are historical. prepare_overlay.py preserves the reference and
checks exact pinned source hashes; it creates only a private import copy.
The receipt records compiled hashes but does not include binary caches.

`python -B verify_artifacts.py` checks exact evidence bytes, source/report
links, guards, conditional scope and prior archives. Add --staged to audit
staged bytes. These checks do not substitute for full kernel replay.
