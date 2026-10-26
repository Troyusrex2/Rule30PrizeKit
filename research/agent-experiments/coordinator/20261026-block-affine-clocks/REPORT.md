# Checked block-affine clocks and further separation experiments

Problem 1 and sink separation remain open. This checkpoint supplies an
independent Lean proof of a known sharper right-diagonal period bound,
together with a generic three-cell return theorem and the exact two-step
rule. The accompanying invariant and rank searches found no certificate.
No new prize essay, API submission or upstream pull request was made.

## The checked clock tool

For every actual one-sided white-boundary history and every depth j,

`a(t + 2^((2*j+1)/3), j) = a(t,j)` for all t,

where `/` is natural-number division. The exponent replaces the earlier
bound j. At depth 12, for example, the supplied clock is 256 rather than
4096. This is a period that works, not a claim that every history has that
least period, or that least periods cannot decrease with depth.

The numerical estimate is already recorded as G249 in the
[placego record map](https://github.com/ghywel/placego/blob/207ebff1abeb05b812aac41c1cd425ab652394bc/RECORD-MAP.md).
No mathematical novelty or first-formalization priority is claimed. Our
proof is independent of that project's proof terms and uses only the
previously checked CommonPast module and official core imports.

The useful return-map mechanism is explicit. For three successive cells,
write the update as

`(x,y,z) -> (x XOR A, y XOR (x OR u), z XOR (y OR x))`.

Two such updates, even with different driving inputs, form an affine
triangular map on three bits (`pair_act`). These maps are closed under
composition and every one has fourth power equal to the identity
(`quartic_act`). Hence any driving word of even period P gives this block
period 4*P (`even_block_period`). Induction adds three spatial depths at a
time and multiplies the prefix clock by four (`prefix_three_step` and
`prefix_clock_families`). Small base cases cover every residue class.

The even-period restriction matters: the constant input (A,u)=(1,0) has
a three-bit orbit that has not returned after four steps. It is included
as a negative control; the proof does not silently apply the lemma to odd P.

The module also proves, for j=n+4, the exact local identity

`a(t+2,j) = a(t,j) XOR ((a(t,j-3) OR a(t,j-4)) AND NOT(a(t,j-2) XOR a(t,j-1)))`.

Thus two updates depend affinely on the latest three cells when the earlier
pair is fixed (`actual_two_step`). This may be useful for recursive block
certificates; no terminating separation recursion is supplied here.

`supported_common_mode_periodic_tighter` transfers the clock to a common
linear mode through actual recombination. It explicitly retains **all-time
Subset**, in addition to Mode and Common. Initial subset is not enough for
this proof, and unconditional preservation has not been established.

## Verification

The final [Rule30BlockClockResearch.lean](work/Rule30BlockClockResearch.lean)
has SHA-256 `180b34d077c5bf36296cddc8d0666e340f9ef1514ca803fa10dbd4305596c9d3`.
All 112 declarations and eight headlines pass the unchanged official checker
at kit commit `0090056412733accaa27643d3cbbf982104f2251`, with no new axioms.
The count includes generated declarations. The final G913 build and full
replay take about 30 seconds, with peak owned RSS 3.02 GB. Its byte-identical
100-declaration CommonPast dependency was freshly rebuilt and replayed too.
No native decision tactic, new axiom or checker modification is used.

Independent controls pass 32,768 affine compositions, 512 fourth powers,
128 two-gate cases and all 32 literal five-cell two-step patterns. Packed
iteration checks every initial row at widths 1 through 13 against the new
clock: 2,976,602 row updates. A separate scalar truth-table control checks
4,674 cells. These Python controls are separate from the kernel proof.

The local Wolfram Engine's built-in CellularAutomaton[30] passes all 510
initial rows of widths 1 through 8, with 88,132 period-cell comparisons
inside valid causal cones. This is local software validation, not Wolfram
backend or human verification.

## Fixed-clock inverse structure: evidence, not an induction

The white-boundary single-profile graph at clock 64 now closes completely:
171,780 states and 171,784 edges, with maximum shortest-word length 106.
There is no nonconstant-OR collision between different current-column
profiles, no drop of least period along an edge, and no merging outside
the period-two core. The corresponding graphs at clocks 2, 4, 8, 16 and 32
also have those properties. An independent literal Rule 30 integrator
rebuilds and checks the counts and properties at all six clocks.

This suggests a uniform inverse-tree target with the white boundary retained.
It does not establish that target at clock 128 or at all clocks, and does
not prove reader completeness. In particular, no monotonicity theorem is
inferred from the census. A boundary-free probe reencounters the known
period-loss phenomenon at clock eight with a cyclic ancestral tail; it
does not give a finite-white-boundary counterexample or a new novelty claim.

## Further failed global proof attempts

Three NFA experiments tested more expressive regular invariants: forward
time words, reversed time words with a learned initial subset, and the
reversed model with phase hints from an earlier nine-state candidate.
The forward bounds 2..8 and reversed bounds 2..8 are reported UNSAT.
Reversed bounds 9..14, including the hinted runs, hit their solver limits.
No candidate reached a closure proof. A timeout is not a proof of UNSAT.

All three retain 337 positives, 350 negatives and 2,741 implications.
An independent audit validates their Rule 30 meanings and 17,472 reverse
carry controls. A separate encoding control forces a known nine-state
model on the facts it satisfies; that control passes. Facts are filtered
only for that explicitly labeled encoding control, never from the actual
searches. Its SAT result is not an invariant certificate.

Context-dependent lexicographic ranks were also tested. With 1..3 retained
recent symbols and 1..3 physical updates, 16 templates are reported UNSAT
and the two largest time out. Prefix parity, position parity, symbol-count
parity and modulo-four prefix counts test information beyond a fixed recent
window: five attempted templates are reported UNSAT and three time out.
The internal deadline stops that run before its two-update cases. None of
these reports is a Lean proof that all possible ranks are impossible.

## External-source audit and remaining work

Four related Lean sources from placego were screened at pinned commit
207ebff1abeb05b812aac41c1cd425ab652394bc. None is used as a proof premise.
RootedReturn uses the other diagonal's reset recurrence, not our accumulator
recurrence; ParityMask's relevant uniqueness assumption is an odd clock,
whereas our nontrivial clocks are even. JenPow2 and LemmaB2 address the
left-diagonal system. Their source hashes and the fact that they were not
kernel-replayed here are recorded. A clean source scan alone is not treated
as kernel verification.

The target is still an all-clock separation proof retaining the white
boundary, or a verified finite-prefix all-time counterexample. The new
block-affine formulation is available for recursive witnesses or a clock
induction; the clock bound by itself supplies neither. The earlier bridge
from sink separation to collision clocks and subset preservation remains
valid. The fixed-center past observation remains separate.

All outer guards remain 300 seconds, 8 GiB owned RSS and 2 GiB minimum free
system memory. All jobs are terminal. See [reproduction notes](REPRODUCE.md)
and the exact source, build, replay, controls and failed-search artifacts.
