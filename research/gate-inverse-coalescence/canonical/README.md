# Canonical catalog adaptation

This directory contains the catalog forms `Ruliology.CellularAutomata.Rule30InverseRuns`, `Rule30GateInverseMerge`, and `Rule30GatePastThree`. Their proof bodies are unchanged from the parent research modules; only module/import/namespace names and LF line endings are adapted. [ADAPTATIONS.json](ADAPTATIONS.json) records the exact source hashes.

The actual contribution checkout passed a fresh core-catalog Lake build of the eleven-source closure, the unchanged checker for all **327 owned constants and 24 headline statements**, and a combined three-import smoke. Each source-build log has zero warnings. No new axioms were introduced. The build/replay took 33.409 seconds; this is not a whole-catalog or Mathlib build. Receipts and types are in [evidence/catalog](evidence/catalog/RESULT.json), with its separate owned-resource guard in `evidence/guard`.

The standalone portable recipe is separately tested in [evidence/portable](evidence/portable/RESULT.json). It reuses the parent's exact eight official source files and unchanged checker, creates a new minimal core-Lake project, builds all eleven sources from scratch, replays all three modules, and checks their combined import. No compiled objects are distributed or reused.

With Lean/Lake 4.35.0 installed:

```text
python canonical/verify.py --audit-only
python canonical/verify.py --lean /path/to/lean --lake /path/to/lake --out /a/new/output/directory
```

For a relocated parent archive, add `--archive /path/to/gate-inverse-coalescence`. This script uses Python's standard library and installs nothing. `INPUTS.json` pins the eleven source hashes and every selected theorem name.

The scope is the same as the parent archive: inverse coalescence and exact finite-support equivalences; locality of a fixed three-bit gate past; no proof of generic predecessor existence, arbitrary-length past editing, Q01, or a prize theorem.
