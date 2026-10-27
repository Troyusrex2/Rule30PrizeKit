# Gated observation periods from a first reset

For an actual finite older list u ≠ [], append two bits g,h and assume the existing all-time Gated condition: the child's even observation is the complement of its penultimate bit, and its odd observation is always black. If both older observation streams have a common period P > 0, then both child observation streams have period P. A whole older P-return is not assumed.

The exact theorem is [gated_observation_period](bundle/sources/Rule30GatedObservationResetResearch.lean), source SHA256 `a73205ebbe1316d2a16fd6716cf077245fbe33b206221ea4088df57562880258`. The [paper](notes/right-gate-reset-audit-20261027T0055/PAPER.md) explains the literal reset latch, its first-period synchronization, and the remaining cover defect. Lists are older-first; observations are the canonical `100` moving-diagonal even/odd channels.

The conclusion concerns observations. It does not establish a whole-child P-return, supply a gate on the older prefix, prove reader completeness, or connect these gates to an arbitrary fixed physical center. No example separating observation periods from whole returns on actual lists is claimed. The general plateau, gate-halving, and physical-center problems remain open, as does Prize Problem 1.

## Verification and exact archive scope

The fresh portable replay rebuilt all 10 research modules from source and fully replayed 812 module-owned constants, 547 non-internal declarations, and 33 selected headlines. Every check passed with standard axioms only and no new axioms. There were 0 build warnings. Counts include generated constants and are derived from the [fresh receipts](reproduction-receipt.json), not treated as counts of handwritten theorems.

An [independent source/type/provenance audit](independent-source-audit/REPORT.md) found no semantic or quantifier defect. It checked the exact source, elaborated headline types, both sealed input packages, and raw official source hashes at both pins. That audit did not run Lean; its approval is distinct from the fresh portable execution recorded here. Original provenance/control scripts are retained as evidence, while bundle/replay.py is the supported standalone Lean reproduction entry point.

The new leaf accounts for 24 replayed constants and 4 headlines. The other modules are its exact previously verified dependency closure; unrelated invariant, linear-barrier, and response-filter modules are excluded. The bundle includes exactly three official source references: Rule30Jen, Rule30Prize, and Rule30Diagonals.

The guarded job completed in 38.08 seconds with 2.626 GiB peak owned RSS and no resource stop. Its limits were 300 seconds, 8 GiB owned RSS, and 2 GiB minimum available memory. Only the immutable official compiled library was reused; every research object was freshly built into a new output directory. This was not a cold build of the full kit or toolchain. See [guard evidence](evidence/run_bundle.guard.json).

The actual compiled reference is kit `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0. All three required official source files are byte-identical at current pin `7d665044b904117af9e82328aeb90a30692b2b85`. [Source references](bundle/summary.json) and [closure compatibility](bundle/CLOSURE-COMPATIBILITY.json) document that distinction. The unchanged checker SHA256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. This archive is research evidence; it does not itself represent an official backend submission or catalog merge.

## Reproduce

Use Python 3 and Lean 4.35.0, with the matching official compiled library and unchanged Check.lean. The output directory must not already exist and must be outside the bundle, official library, and toolchain.

```text
python bundle/replay.py --verify-only
python bundle/replay.py --lean /path/to/lean --official-lib /path/to/kit/.lake/build/lib/lean --checker /path/to/kit/Check.lean --output /path/to/new-output
```

The replay verifies bundle hashes, freshly compiles the ten research modules in dependency order, then runs the complete checker on every module and its selected headlines. It loads no private precompiled research modules. The three official source snapshots are references for the external official library and are not silently substituted on the import path. Prior receipts are provenance; new totals are computed from the new checker results. All frozen original packages remained unchanged.

## Paper-only route failures

- [Adjacent-pair quadratic cycle parity](notes/ca-phase-quadratic-parity-20261027T0056/REPORT.md): the proposed phase orientation fails on the named actual three-bit tail `000`, even at its least whole clock. The original convention mistake and corrected structural counterexample are retained. This does not refute nonlinear observation.
- [Full temporal algebraic closure](notes/clock-birth-algebra-closure-20261027T0100/PAPER.md): unlabeled generated ideals/modules/algebras discard the marked ordered-parent information needed to evaluate K. Read its [clock convention](notes/clock-birth-algebra-closure-20261027T0100/CLOCK-CONVENTION.md); the oldest-defect application requires a least whole clock or explicit half-return failure. This does not disprove the desired finite-white K=0 implication or richer marked invariants.

These two routes are paper-only, not Lean theorems. The reset paper's forced-latch/cover-defect discussion and named controls are also separate from the formal observation-period theorem. No state/period/width sweep or public API essay is part of this archive. [SOURCE-MAP.json](SOURCE-MAP.json) maps original workspace references to these copies. artifacts.json hashes every archive file except itself.
