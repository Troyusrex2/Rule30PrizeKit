# Physical Rule30 birth barriers

Two kernel-checked results identify information a successful birth-budget argument must use. They do not solve a Rule30 Prize problem.

1. **A physical periodic counterexample.** An exact bi-infinite Rule30 spacetime has a period-2 center and a period-6 right neighbor that fails period4. Comparing this orbit with itself four ticks earlier gives a true mismatch birth at every time `6*k+4`. The proof constructs N distinct births with both readings before time `6*N`. The initial row has infinite support.
2. **A uniform finite-window obstruction.** For every radius R, no integer-valued potential depending only on the two physical windows at times t and t-4 and phase `t mod4` can pay every true birth while never increasing, for all finite nonzero configurations satisfying the specified finite local alternating-center condition. The proof cuts the periodic row to a finite interval and uses official Rule30 locality. Its observations at4 and16 agree despite births at4 and10.

The second statement uses a finite local center premise, not an all-time periodicity premise. It leaves whole-row or unbounded-ancestry potentials, boundary reserves, and single-seed-specific arguments open. The formal codomain is `Int`; the accompanying paper discusses a real-valued extension, which is not presented as a Lean theorem. No edge-position strengthening is included in the verified headlines.

## Sources and evidence

The matching source contribution is [commit805db8e](https://github.com/Troyusrex2/Rule30PrizeKit/tree/805db8e66925f8706616edcefe705341b844db0f). No pull-request number is assumed here.

The canonical modules are [Rule30PeriodicBirthCounterexample](Ruliology/CellularAutomata/Rule30PeriodicBirthCounterexample.lean) and [Rule30LocalBirthPotential](Ruliology/CellularAutomata/Rule30LocalBirthPotential.lean). The latter uses the official [arbitrary-row evolution](Ruliology/CellularAutomata/Rule30Realization.lean) and [locality theorem](Ruliology/CellularAutomata/Rule30ZeroBoundaryBarriers.lean), rather than defining another automaton. The official dependencies are exact sources at pin `7d665044b904117af9e82328aeb90a30692b2b85`.

The final integrated validation freshly built all **12 sources** with actual Lake, then replayed all **89 owned constants and 17 headlines** using the unchanged official checker. The source build had zero warnings; the checker retains its existing replay-API deprecation warning. No new axioms or native decision procedures are used. See the [full result](evidence/canonical-lake/RESULT.json), [printed types](evidence/canonical-lake/Types.log), and [resource receipt extract](evidence/canonical-lake/RESOURCE-EXTRACT.json).

Actual Lake build:18.4468 seconds. Entire guarded build/check/type job:21.7897 seconds, peak owned RSS1,862,021,120 bytes, minimum available system memory43,945,197,568 bytes; no guard stop. This archive preparation performed no additional proof build.

[SOURCE-MAP.json](SOURCE-MAP.json) verifies that both research proof bodies are unchanged under the canonical namespace/header conversion. [PROOF.md](PROOF.md) gives the argument and its limits. Independent static reviews are under `audits/`; historical author receipts and explicitly labeled failed-attempt records are under `evidence/author-*` and `history/`. Historical failures are not proof evidence.

## Reproduce

Use the existing pinned Lean4.35 toolchain specified by `lean-toolchain`. This is a core-Lean project with no Mathlib or external package dependency. It includes source only, without compiled objects.

```sh
lake build Ruliology.CellularAutomata.Rule30PeriodicBirthCounterexample Ruliology.CellularAutomata.Rule30LocalBirthPotential
lake env python verify.py --run-name independent
```

`verify.py` checks the source/checker hashes in `SOURCES.json`, clears inherited library paths, compiles all12 sources into a new empty library, runs unchanged `Check.lean` on both owned modules with all17 headline arguments, and prints the types and axioms. It records outputs in a new `runs/independent` directory; use a new run name for another replay. The script was statically reviewed here; the recorded successful execution is the separate actual-Lake validation described above.

For a direct single-headline check after Lake build:

```sh
lake env lean --run Check.lean Ruliology.CellularAutomata.Rule30LocalBirthPotential --claim partial --headline Ruliology.CellularAutomata.Rule30LocalBirthPotential.no_local_birth_potential
```

The unchanged checker SHA256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. Exact source hashes, module order, expected constants and all headline names are in `SOURCES.json`.

The optional `exploration/` records preserve the bounded discovery protocols, saved cycle, and independent scalar orientation audits. None is required to rerun a search to check the Lean proofs. Scalar audits, paper arguments and kernel proofs are labeled separately. Run exploratory scripts only in a disposable copy if preserving their original output receipts matters.

Work prepared for Troy Lowry with OpenAI Codex assistance. No prize submission or submission-service evaluation is claimed by this archive. Private command paths and runtime details were omitted only through the documented extracts in [provenance](provenance/PACKAGING-CORRECTIONS.json); their original hashes are retained.
