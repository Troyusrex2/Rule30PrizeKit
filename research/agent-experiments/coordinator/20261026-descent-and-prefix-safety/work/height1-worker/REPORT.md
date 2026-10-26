# Height-one transfer to a strictly shorter Safe counterexample

The new strongest theorem is `HeightOneDescent.height_one_nonreturn_shorter`:

```lean
theorem height_one_nonreturn_shorter (xs : List Bool)
    (hh : SpanOne (tr xs)) (hn : evolution 8 xs ≠ xs) :
    ∃ ys : List Bool, ys.length + 1 = xs.length ∧
      CedarSafety.Safe ys ∧ evolution 8 ys ≠ ys
```

Here `xs` is any genuine finite-white word in older-first order. `tr xs`
is literally the newest bit of its finite-list evolution, not a freely
assigned temporal profile. `SpanOne` means that the signed WHITE-event
height stays in a single interval `[lo, lo + 1]` for every natural time.
`Safe` forbids consecutive temporal zeroes in the newest trace. Return
means return of the ENTIRE word. The witness is its immediate parent
prefix with only that parent's newest initial bit complemented.

This theorem assumes neither global Safe completeness nor D3, and needs
no supplied column period. It also covers a low-period newest column
whose older prefix might otherwise conceal nonreturn.

## Kernel-verified results

| Module | Declarations replayed | Exact source SHA256 |
|---|---:|---|
| HeightOneLogic | 30 | a8421f7776feb9c2c65e474006a3e5c9d8b06f3509703f6333a02a96c8cb8908 |
| HeightOneSemantics | 67 | a80a984938dd74b76e09776dfa976fdb14fbc58635405bfe4a83446cb42d2c6a |
| HeightOneTransfer | 22 | ce1ab3a7e2d406f7f6ad814326c38fa2032db756e9db6d44535f3cb9619d712d |
| HeightOnePeriodicity | 46 | 96d7575d1db70090da3aa05d5cd187dafcb72648772964a11aadeb95de7b069c |
| HeightOneDescent | 13 | a885271f7a288bfac35b06a07d9f8ec6e73de3e809dfd36cfed33b93523b2c40 |

All 178 declarations passed the unchanged official full kernel replay.
The first three modules also passed the root agent's independent replay
of their exact frozen sources (119 declarations); the root has the two
later exact sources for independent review. Worker receipts are under
`formal/<module>/`, with exact-byte `source.lean`, build log, check log and
`report.json`. Guard receipts are under `evidence/`.

Official pin: `5473ffd075f63c9d626e63b8455805d4831b39ca`.
Unchanged checker SHA256:
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
No sorry, new axiom, native decision procedure, checker weakening, or
shared-reference edits were used. Each leaf ran under a 300-second,
8-GiB-owned-RSS, 2-GiB-minimum-free-memory guard. The final two leaves
took 5.98 and 6.09 seconds, with peak owned RSS under 1.29 GiB.

## Exact proof and scope

1. Height-one excludes temporal `010`. The genuine no11011 theorem,
   together with positive column periodicity to handle time zero,
   excludes `101`. Thus every transition of the newest trace is isolated.
2. Write the actual last columns as `... w v u a b`. The three shared
   recurrences force `a = u = D b` at every time, where
   `D b(t) = xor (b(t)) (b(t+1))`. This step is a local Boolean argument
   using actual shared predecessors, not a free strip assumption.
3. Complementing `a` by flipping its initial leaf bit is a genuine
   finite-white operation. The resulting newest trace has no `00`,
   because `D b` has no adjacent ones. Leaf-flip commutes with every
   whole-word iterate in the exact return equivalence used here.
4. Hypothetically suppose this shorter Safe word returned after eight
   steps. Flip back to recover return of the original parent prefix.
   The 36-state catalog covers ALL whole F8 returns. Its equal-pair
   certificate, applied to every evolved row, makes `a = u` two-periodic.
   This is a conditional classification using the hypothetical return;
   no unconditional twin rigidity is assumed.
5. Since `D b = a`, four increments cancel and `b` is four-periodic.
   The parent prefix returns after eight, and `b(8) = b(0)`. Literal
   `evolution_snoc` therefore returns the whole original word after eight,
   contrary to its assumed nonreturn. Widths at most two return directly.

`HeightOneTransfer.height_one_shorter_counterexample` is the initial
Cedar interface: positive even COLUMN period P, height closed at P,
height span at most one on `0..P`, and failure of column period four imply
the same shorter witness. Closed even periodic height is first extended
to all time; a finite window is never substituted for all-time safety.

`HeightOnePeriodicity` transports the existing unconditional
`Rule30CommonPastResearch.actual_periodic` theorem to literal finite-word
evolution. It supplies a positive even column period for every word.
An all-time bounded height then has zero drift. Consequently its
`alltime_height_one_shorter_counterexample` and
`least_column_above_four_transfer` require no added clock hypothesis.
The latter defines least COLUMN period explicitly and never identifies
it with the clock of the whole prefix.

## Minimal-counterexample consequence and remaining gap

`height_one_return_of_shorter_completeness` proves: if every Safe word
strictly shorter than xs returns F8, then any height-one xs itself returns
F8 as a whole. Thus `minimal_safe_counterexample_not_height_one` excludes
height span at most one for a minimum-width Safe/nonreturn counterexample.
This applies without assuming that counterexample's newest column has
large least period.

The converse descent is still missing. Safety bounds the signed height
of the ZERO-PAIR DRIVER of the last two parents; that driver is not, in
general, an actual spatial column. Nothing here turns that driver height
bound into an actual height-one ancestor, or handles the branching in
height two. Therefore this is a genuine counterexample-transfer theorem
and minimal-width obstruction, not Safe completeness, D3, sink separation,
or Prize P1. In particular, it says nothing by itself about the moving
depth `U+t` representing the fixed physical center.

## Dependencies and reproduction

The sealed Cedar v05 package
`r30-codex-cedar-d3-20261026-0704c91b-v05` has manifest SHA256
`69b76bbf7f35176f56f9d952d13949ba3eb5364977b353f95bb07d5020f9d334`.
All 460 files were hash-checked. Cedar's HEIGHT_STAGE and HEIGHT_AUDIT
provided the audited paper transfer; no Cedar file was modified.

Eight exact dependency sources are copied under `dependencies/`, with
their prior full-replay receipts under `dependency-receipts/`:

* RootEventHeight: `height-converse-review-20261026T1854`.
* CedarSafetySoundness, CedarSafetySemantics, CedarSafetyBridge,
  CedarWhiteTransport, RootShortExtensionCore:
  `short-extension-root-review-20261026T1840`.
* CedarNo11011: `tc-cylinder-root-review-20261026T1916`.
* Rule30CommonPastResearch: `return8-bridge-review-20261026T1942`.

`sources.json` records the exact dependency source and compiled hashes.
`prepare.py` checks those and Cedar's full manifest; `replay.py` verifies
the unchanged checker and dependency hashes before each compile/replay.
Replay order is Logic, Semantics, Transfer, Periodicity, Descent. Each
command is `python guard.py replay.py <module>` in the owned G913 folder;
the guard never signals unrelated processes. `verify_artifacts.py`
verifies the local delivery manifest, all frozen source/receipt matches,
all headline passes, and all successful guard exits without launching Lean.

No publication, PR, or submission API action was performed by this worker.
