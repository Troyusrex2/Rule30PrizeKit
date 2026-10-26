# Canonical forms of the sound Rule 30 reader

We proved, with the unchanged reference Lean checker, that the learned sound
reader defines an equivalence relation and admits unique canonical words at
every length. Normalization commutes with the sheared Rule 30 update. Full
reader completeness is now reduced, in both directions, to injectivity of
last-column traces on this invariant canonical language.

**This does not prove that injectivity, Q01, or Prize Problem 1.** These are
local full-kernel checks, not a Wolfram backend or human verification verdict.
No new prize submission or claim of mathematical priority is made.

## All-width theorems

The underlying update, with white boundary, is

`x[j]' = x[j] XOR (x[j-1] OR x[j-2])`, with missing inputs zero.

Read words from the boundary toward increasing depth. The reader's alphabet
is paired bits; its 17-state table is unchanged from the earlier soundness
proof. An accepted paired word has equal last-column traces for all time.

`Rule30ReaderEquivalenceResearch.lean` proves reflexivity, symmetry and
transitivity at every width. Its finite invariants have respectively 3,
17 and 151 reachable states. These are proofs over arbitrary words, not
an enumeration up to a chosen width. The module also supplies
`shared_representative` and `related_sound`.

`Rule30ReaderCanonicalResearch.lean` defines a seven-state canonical DFA.
Its language has the direct description

`0* Sigma^{<=2}  union  0* 1 (00|11) Sigma+`.

Thus either the first one lies among the final two positions, or it is
followed by two equal bits and at least one further bit. The formal
definition is the DFA; the displayed regular expression is an explanatory
description, independently cross-checked on all words through length 14.

The new results are:

- `canonical_exists`: every input word has a same-length, accepted paired
  word whose other projection is canonical. A 21-state determinized
  projection automaton supplies a checked backward-lifting certificate.
- `canonical_unique`: an accepted pair of canonical words has identical
  projections. An 86-state invariant includes a flag for any differing bit.
- `canonical_step`: canonical membership is preserved, in both directions,
  by one white-boundary update, using a 14-state coupled invariant.
- `same_iff_normal_eq`: two words are reader-equivalent exactly when their
  unique normal forms agree. `normal` uses standard `Classical.choose`;
  it is not presented as an executable normalization algorithm.
- `normal_step`: normalization commutes with the actual update.
- `canonical_completeness_reduction`: injectivity of all-time last-column
  traces on equal-length canonical words is equivalent to full reader
  completeness on arbitrary equal-length words. The observer premise is
  **open**, not a proven invariant.
- `canonical_count`: the explicit generator of all Boolean words of length
  `n+3` has exactly `2^(n+2)` canonical entries, for every natural `n`.
  It is proved by a seven-coordinate counting recurrence, not inferred
  from the finite census below.

This identifies the reader's classes uniformly. It does not establish that
different classes have different traces. In particular, the class count
cannot be substituted for a proof of dynamical observability.

## Full-kernel validation

All modules import the official core through the unchanged CommonPast
dependency and were rebuilt in the reference project on G913. The pin is
`0090056412733accaa27643d3cbbf982104f2251`; the checker hash is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

| Module | Replayed declarations | Headlines | Source SHA-256 |
|---|---:|---:|---|
| CommonPast | 100 | 7 | `17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3` |
| ColumnReader | 119 | 3 | `ad1d09b6d460b1849017fcf7c99151ad0304ceee8dfc80e78f43bfc1a917da3b` |
| ReaderEquivalence | 83 | 5 | `574920fd28265f590b6f030784bb22979770f0fb1da023f328825bc3cade6dd7` |
| ReaderCanonical | 215 | 7 | `832fd7632331f8ad6101bc4725a7b954e81e692843017c7df529a52a3901641a` |

Every declaration passed kernel replay, with no new axioms. Standard choice
in the normal-form definition is permitted by the official checker. The
proofs do not use `sorry`, custom axioms, native decision shortcuts, skipped
kernel checking, changed official statements, or a modified checker.

## Exact finite orbit census

As a diagnostic, `orbit_partition.py` enumerates the finite permutation
`F(x)=(x XOR ((x<<1)|(x<<2))) mod 2^width`. It extracts each orbit's cyclic
last-bit word, reduces it to primitive period, and groups exact rotated
profiles. Hashing selects a collision chain only: every candidate match
is compared bit for bit. It then checks every state against an actual
representative with the same full cyclic head profile. The equivalence
theorem explains why this representative check covers all same-profile
pairs without quadratic pair enumeration.

Local widths 1 through 24 and G913 widths 25 through 30 completed with no
counterexample. Width 8 was repeated on both machines. At width 30:

| Quantity | Count |
|---|---:|
| Configurations enumerated | 1,073,741,824 |
| Permutation orbits | 321,518 |
| Primitive necklaces | 114,201 |
| Distinct phased column profiles | 536,870,912 |
| Nontrivial representative reader checks | 536,870,912 |
| Maximum orbit period | 65,536 |

No cycle in this census had a shorter head period than its state period.
No hash collisions were encountered, but the algorithm does not rely on
their absence. The G913 run used under 4 GB of sampled owned RSS and about
93 seconds including compilation and all widths 25 through 30.

This computation is **finite Python/Numba evidence**, not a Lean theorem
about width 30 or all widths. The clock cap comes from the previous checked
block-clock bound and is asserted by the program. A longer orbit or a
failed exact match would stop the run rather than be discarded.

Independent controls passed:

- 669,924 literal truth-table cells, 87,380 all-pair comparisons through
  width 8, and 8,190 brute minimal-rotation controls.
- Canonical witnesses and the direct language test for all 32,767 words
  through width 14; 425,986 literal Rule 30 update cells; all 21,861
  canonical pairs through width 8.
- Local Wolfram Language 15's built-in `CellularAutomaton[30,...]` confirmed
  canonical membership invariance for 2,046 initial rows through width 10,
  covering 18,434 sheared cells. No cloud authentication was involved.

## Failed rank synthesis

The canonical reduction justifies restricting a separation search to
canonical rows. `canonical_rank.py` tries lexicographic word ranks whose
digits depend on reader state, both canonical states, and zero, one, or
two previous paired symbols. It tries one, two, or three time updates and
both first- and last-difference dominance. All 18 finite synthesis instances
returned UNSAT. No rank certificate or general impossibility theorem was
obtained. These failed templates do not refute the canonical observer.

## What remains

The next useful proof is an unbounded canonical observer, or a counterexample
to it. A recursive orbit/inverse-tree argument is a possible direction;
increasing the census width alone does not settle that question. If full
reader completeness is proved, the already checked collision bridge gives
CollisionClock and the finite-defect preservation consequence. Connecting
this sheared left-boundary system to the fixed physical center is a further
open step. No implication to the prize has been silently assumed.

The public submissions and local response inbox were refreshed at
2026-10-26 07:53 UTC: 40 public entries, no changed or new entries, no new
READY responses or revisions since the seven round-three responses. The
reference environment and skill 1.17.3 were unchanged.

Sources, tests, reports, guard logs and a hash manifest accompany this
report. Earlier archive hashes remain unchanged. See `REPRODUCE.md` and
run `verify_artifacts.py` to check the selected artifact bytes and claims.
