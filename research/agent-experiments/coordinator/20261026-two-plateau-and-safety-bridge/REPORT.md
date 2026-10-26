# A second plateau obstruction and an exact safety-language bridge

Two unbounded partial results now pass full replay through the unchanged
official Lean checker. The clock argument excludes one more plateau at
every even clock length. The Cedar team identifies exactly which safe
finite words also return after eight updates. **Safety completeness and
Rule 30 Prize Problem 1 remain open.** These are local full-kernel checks,
not new Wolfram backend or human verification verdicts.

## Uniform clock exclusion

In an Actual triangular history, write six consecutive columns, older to
newer, as n,m,l,k,h,g. Their updates from l onward are the literal rule
`x' = x XOR (previous OR older)`. Suppose k flips after an even time R and
l repeats after R. Then g OR h cannot be constantly one.

The theorem is
`Rule30TwoPlateauRigidityResearch.actual_even_two_plateau_or_impossible`:
for all histories a, positions j and natural n, if a(j+3) is anti-(2n) and
a(j+2) is (2n)-periodic, then it is false that a(j+5) OR a(j+4)=1 at every
time. No period is supplied for the newer pair or the unspecified older
columns. The earlier theorem put the antiperiodic source inside the OR
pair; this result puts it one cell farther back.

First, `actual_saturated_or_double_period` proves that a constant saturated
OR would force both newer profiles h,g to repeat after 2R. A periodic XOR
driver gives a constant shift flag. The earlier even-clock rigidity lemma
eliminates a nonzero flag for h; a forced zero of h eliminates g's flag.
This preliminary theorem covers every R, not only even R.

Next, compare the six-cell strip at times t and t+R. Its two oldest inputs
are free at every time in each copy. The pair has opposite k values, equal
l values, and saturated newest OR in both copies. Three exact backward
viability steps reduce 576 paired states to 152,92,70. Every actual all-time
path belongs to the last set. For its 16 possible projections onto the
upper four cells in each copy, a finite invariant is initialized, preserved
by two graph transitions, and excludes the swapped projection. Induction
proves this for every even path length. But the derived 2R periods force
the projection to swap after R, a contradiction when R is even.

The certificate contains 366 projected even-reachability pairs. It is
not a census of temporal clocks: the Lean path induction has no length
bound. Data and semantic proof modules were separately replayed in full.
Literal cell controls independently check the packed local update.

## Cedar's exact limited classification

Credit: the Codex Cedar research team working for Troy Lowry, through the
two response identifiers in provenance.json. We verified all 152 and 140
artifact hashes in those sealed handoffs, reviewed the exact statements,
and independently replayed each included formal module.

`CedarSafetySoundness.accepted_return_eight` proves that every finite word
accepted by the existing 13-state DFA returns as a WHOLE word after eight
literal finite-white triangular updates. Its spatial induction uses a
28-state profile certificate. This strengthens the earlier construction's
newest-trace safety; it does not prove acceptance of every safe word.

`CedarSafetyBridge.safe_return_iff_accepted` proves, for every finite list,

    (Safe xs AND evolution 8 xs = xs) iff accepted(read 0 xs)=true.

Safe is exactly the all-time absence of two consecutive newest zeros,
with `getLastD false`; the empty word is correctly unsafe. A 36-live-state
profile automaton (plus a dead state) and spatial induction connect the
finite eight-edge check to literal F. Full-word return makes that finite
window equivalent to all-time safety. Thus the still-open statements
Safe=>return8 and Safe=>acceptance are now proved equivalent. Neither is
proved true by this bridge.

`CedarWhiteTransport` proves leading-white invariance, prefix autonomy and
the exact dependency-cone identity

    drop(n+2t)(evolution t xs) = drop(2t)(evolution t (drop n xs)).

It also transports a common suffix outside that cone. These elementary
semantic tools do not formalize the earlier special-family erosion formula.
The team's short-extension, seed-class and further descent experiments are
not adopted here as Lean results. Their continuing completeness work is
separate from the checked conditional equivalence.

## Controls and remaining gaps

A proposed reset from a periodic physical driver containing 11 fails in
the free-outer-boundary graph at every tested width1..10 for 110,1011,1100.
At width10, exact noncommuting closed walks give different equal-length
output blocks of lengths57,100,48. Every edge has an independent scalar
audit. Such paths are not asserted to arise from finite initial rows.
Literal finite-right experiments show different behavior for different
drivers; their observed tail periods are finite evidence only.

A second control concerns two successive clock doublings. Six-cell cyclic
relaxations can have k anti-R, h anti-(2R), and a safe newest g, even when
all supplied older profiles repeat after R. There are literal SAT witnesses
at R=2,4,8,16. The oldest two profiles are arbitrary inputs; these are NOT
genuine finite-white prefixes. The independent audit checks every update,
all clock premises, safety and white-boundary failures. The genuine finite
white word [1,0,0,0,0,1] is a positive R=2 control. This warns against
replacing genuine white ancestry by a few periodic older profiles.

The stronger source-two-periodicity shortcut and a global one-bit phase
coloring also fail on the paired graph; retained scripts/data show why the
proved two-step relational invariant is needed. Earlier cyclic SAT checks
remain diagnostic controls, not premises of the unbounded theorem.

The physical center reads changing diagonal depths. Neither clock rigidity
nor the conditional safety-language equivalence supplies that observer
bridge. No full prize statement or new prize submission is claimed.

## Validation

Pin5473ffd075f63c9d626e63b8455805d4831b39ca, Lean4.35.0; Check.lean SHA-256
b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905.

| Module | Fully replayed constants | Headline scope |
|---|---:|---|
| Rule30SaturatedOrPeriodResearch | 8 | Derived periods of the newer pair |
| Rule30PlateauPairCertificate | 122 | Exact graph and invariant checks |
| Rule30TwoPlateauRigidityResearch | 48 | All-even-clock plateau exclusion |
| CedarSafetySoundness | 137 | All-width accepted full-word return |
| CedarSafetySemantics | 75 | Exact all-time safety/window bridge |
| CedarSafetyBridge | 8 | Conditional language equivalence |
| CedarWhiteTransport | 18 | Prefix, padding and dependency cone |

Counts include definitions, generated declarations and computation tables,
not independent discoveries. No new axioms or native decisions are used.
The root clock jobs took1.54,5.35,2.78 seconds for compilation plus replay,
with sampled peaks721,892,846 MiB. Cedar soundness was independently rebuilt
from pinned Git objects without reference-cache reuse and replayed in8.69s
at750 MiB; the three later modules independently replayed in5.87s at762 MiB.
Every successful guarded job retained the300s/8GiB-owned/2GiB-free limits.
Two repaired elaboration attempts are preserved and are not counted as passes.

See REPRODUCE.md for source order and full-check commands. Run
`python -B verify_artifacts.py`, or add `--staged`, to audit exact bytes,
report/source linkage, unchanged checker, resources and claim scope.
This artifact audit does not replace kernel replay.
