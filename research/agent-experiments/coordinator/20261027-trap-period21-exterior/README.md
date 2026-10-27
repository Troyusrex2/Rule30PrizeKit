# The 001 trap has no full period21 right extension

`Rule30TrapPeriod21.no_period21_trapped` proves that an actual Rule30 right-half history entering any correctly aligned `t001` state cannot have temporal period21 in every column. The driver may become001-periodic at an arbitrary onset, and the trap entry may have any admissible label. The physical history and common21-period premise are explicit in the theorem type.

The trap's periodic head is therefore compatible with an exterior that does not have that same period. This result does not prove `AbsorptionT t001`, exclude longer exterior periods, or solve Problem1. It does not claim that the whole47-column strip repeats after21 ticks. The optional extension to individually eventual21-periodic columns with different onsets has not been formalized here.

Three catalog-shaped modules are included:

* [Rule30Period21Profiles](Ruliology/CellularAutomata/Rule30Period21Profiles.lean): exact profile predecessor, safe-path checker, and finite inverse-history argument using the official core-Lean pigeonhole theorem.
* [Rule30Certificates.TrapPeriod21](Ruliology/CellularAutomata/Rule30Certificates/TrapPeriod21.lean):206 checked numeric segments and their closed-cycle composition.
* [Rule30TrapPeriod21](Ruliology/CellularAutomata/Rule30TrapPeriod21.lean): temporal packing, the literal physical bridge, full head projection of all815 trap states, and normalization of every entry label.

The sources follow the catalog's `module`, public-import, exposed-public-section, and `Ruliology.CellularAutomata` namespace conventions. Eight unchanged official dependencies are included from commit `7d665044b904117af9e82328aeb90a30692b2b85`. This candidate uses **core Lean4.35.0 only**, without Mathlib or any downloaded package dependency.

## Reproduce

With Lean4.35.0 available, run from this directory:

```text
python verify.py --lean lean
```

`lake env python verify.py` is also suitable when Lake selects the included toolchain. The script compiles all11 sources into a new empty library, clears inherited `LEAN_PATH`, runs the unchanged official checker on all three contribution modules and all13 headline types, and prints their axioms. Output is under a new `runs/` directory. No SSH, private reference checkout, compiled contribution object, or Mathlib cache is required.

The required catalog commands were also run separately on these same frozen sources:

```text
lake build Ruliology.CellularAutomata.Rule30TrapPeriod21
lake env lean --run Check.lean Ruliology.CellularAutomata.Rule30TrapPeriod21 --claim partial --headline Ruliology.CellularAutomata.Rule30TrapPeriod21.no_period21_trapped
```

Both passed. The [distinct Lake receipts](evidence/lake-smoke/RESULT.json) record13.92 seconds for the actual build and1.33 seconds for the named-head invocation (the main module's46 constants replayed). The complete guarded smoke run used15.39 seconds and peaked at840,167,424 bytes. This supplements the full three-module728/13 reproduction rather than replacing it.

The checked-in [fresh reproduction receipts](evidence/fresh11/RESULT.json) report **728 owned constants and13 headline types**, all passing with no new axioms. All11 source build logs contain no warnings. Raw checker stdout retains the official `Lean.Environment.replay` deprecation warning. No global warning-free-log claim is made.

The measured complete guarded job took24.18 seconds and peaked at815,616,000 bytes (about0.76GiB), including source builds, complete replay, and printed types. Thus the observed total run, and consequently every contained module, stayed below the catalog's60-second/4GiB bounds. The guard itself used300 seconds/8GiB/2GiB minimum free memory; its command-free resource extract records the original guard hash. These are measured results on one machine, not guaranteed timings elsewhere.

The checker is unchanged, SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. Sources and metadata are recorded in [SOURCES.json](SOURCES.json); [MANIFEST.json](MANIFEST.json) seals the portable payload. The complete proof outline is in [PROOF.md](PROOF.md).

The earlier Mathlib-backed author version also passed728/13 and remains separately sealed. This fresh core-only result was not inferred from those receipts: all11 sources and all owned constants were rebuilt and replayed after the pigeonhole port and namespace transformation. The source map records the changes and preserves the distinction.

Prepared for Troy Lowry with OpenAI Codex. The original `t001` certificate, its invariant, the actual Rule30 definitions, and Jen's finite pigeonhole theorem are existing official work reused with their exact sources. This directory is a review candidate, not a prize submission.
