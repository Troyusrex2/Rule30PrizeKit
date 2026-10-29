# Arbitrary-driver masking and a conditional all-period bridge

**The Rule30 prize remains open. The exclusion hypothesis defined here is not proved.**

This package formalizes an arbitrary-driver version of the kit's effective-boundary argument and makes one proposed all-period route to the official Problem1 explicit. It does not identify its assertion with the catalog's informal LHC by fiat, prove that assertion, or claim a new nonperiodicity result.

Let `L c s t p` be the official driven left half, with driver `c : Nat -> Bool`, initial state `s : Int -> Bool`, and `p<0`. Set `effective c t = c t && c(t+1)`.

The main unconditional statements are:

- `transport_iff_falling`: the two evolutions driven by `c` and `effective c` agree at every negative position and every time **iff** `L c s t (-1)=true` at every `10` transition of `c`. No periodicity or finite-start hypothesis is needed.
- `consistency_iff`: the necessary black-time consistency conditions are equivalent for the two drivers. The condition says that whenever `c t=true`, the left neighbor is `!c(t+1)`.
- `consistent_transport`: either full consistency condition supplies the falling-transition pins and hence transport. The `11` condition matters to full consistency, but is unnecessary for equality of the driven evolutions.

The generic proof `driven_eq_of_mask` uses induction on time. Only position-1 sees the driver; equality of its OR-masked inputs preserves the next row. Necessity of the falling pins follows by comparing the next value at-1 and canceling the identical older neighbor. This generalizes the actual-center specialization in the kit; it makes no claim of priority for the elementary masking observation.

`PeriodicMaskExclusion` is a **definition of an open assertion**: for every periodic driver of positive period taking both Boolean values, and every start with a leftmost black cell strictly left of zero and white cells farther left, the effective-driven black-time consistency condition fails.

`problem1_of_periodic_mask_exclusion` proves the precise CONDITIONAL theorem

```text
PeriodicMaskExclusion -> Ruliology.CellularAutomata.Rule30Prize.Problem1
```

It restarts a hypothetical eventually periodic actual center at a positive time after its onset, uses the actual finite nonzero left start and its expanding black edge, and transfers actual consistency to the effective driver. Existing exclusion of eventual constancy ensures that every center tail takes both values. The open assertion then gives the contradiction. No hypothesis is discharged by naming it, and no new axiom is introduced. This route may be stronger than the single-seed prize target.

The pair of the effective driver AND the original mask remains essential; the effective driver alone loses the times at which the constraints apply. This is an all-period bridge, not a claim that the previous S-legal period-two closing criterion already handles all periods.

## Verification and replay

Reference: Windows official Lean4.35.0; four unchanged official source dependencies pinned to `932cf8dde039b89b1dcbe9636867bb1b2057fef0`. The unchanged official `Check.lean` is included and hash-pinned.

```text
python verify.py --lean C:/path/to/lean.exe --out C:/new/empty/output
```

Python3 and sibling `lean`/`lake` are required. No downloads or Mathlib are needed. The script checks the package hashes, copies source files into a fresh output directory, clears inherited Lean search-path overrides, builds all five modules with one worker, and replays all declarations owned by `MaskedTransport`. Standard-library toolchain objects are used; no owned objects are reused. Each command has a180-second timeout. The output directory must not exist.

The reference fresh-source check passed: **28 owned declarations,10 selected headlines, no research-source warnings, standard axioms only**. Counts include definitions/helpers, not28 major results. This is a focused closure build, not a whole-catalog or cold standard-library build.

The official check is run with `--claim partial`, which accepts arbitrary theorem TYPES for human review; it is not a prize check. `Types.log` records the actual types and axioms. Additional compiled type guards check the exact transport equivalence and the implication to the official Problem1 with the open hypothesis retained. The checker emits its existing replay-deprecation warning and is not modified.

`evidence/RESULT.json` records the reference receipt and explicitly marks `open_exclusion_hypothesis_proved=false` and `prize_solution=false`. `SOURCE-HASHES.json` freezes all payloads except itself. Cross-platform execution uses a different official executable hash and has not been independently tested here.

## Provenance

Developed by Troy Lowry with OpenAI Codex following a reciprocal written review with independent Claude/swarm. The source-level all-period assertion was formulated explicitly by root; swarm supplied the paper transport proof and its falling-transition sharpening. Root checked sufficiency, added the necessity equivalence, and formalized the conditional prize bridge. The underlying effective-boundary observation is already in the official `Rule30MaskedJen` and `Rule30DrivenLeft` modules.

This package contains mathematical source and evidence only. No claim of upstream acceptance or a formal Wolfram submission is made.
