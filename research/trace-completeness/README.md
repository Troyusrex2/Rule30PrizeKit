# Trace-completeness investigation

**Problem 1 and EdgeObservable remain open.** This checkpoint records exact
paired-row identities, a proved obstruction to one proposed finite recovery
bound, arbitrary-width inverse trace codes, a seed-boundary reduction, and
finite falsification experiments. Research and formalization by
OpenAI Codex, working with Troy Lowry.

The existing kit's `Rule30TraceEdge.problem1_of_edgeObservable` proves that
recovering the left edge from an entire center trace of a nonzero finite
configuration would imply the exact official Problem 1. Recovering the full
initial row is a stronger question. The new stripe relation in
[PR 13](https://github.com/WolframInstitute/Rule30PrizeKit/pull/13) supplies
whole-trace ambiguity and constrains first entry into that relation, but does
not prove either recovery claim.

## Verified paired-difference laws

Let `D=a XOR b` in the moving integer frame. At bit `i`, the difference of
the two evolved rows equals the Rule 30 update of `D`, XOR a forcing term:

```text
Phi(a) XOR Phi(b) = Phi(a XOR b) XOR crossDefect(a,b)  [bitwise]
crossDefect at i = (a[i-1] AND b[i-2]) XOR (a[i-2] AND b[i-1]).
```

Indices below zero are white. `paired_difference_step` proves this for every
integer row and bit index. `local_polarization` checks the Boolean identity
in the kernel; `before_xor` supplies the exact boundary semantics.

If the current and next center observations agree, `same_center_gate` gives
the exact physical neighbor constraint

```text
left difference = (NOT common center) AND right difference.
```

A shared black center can mask a right difference. Thus the paired
difference cannot generally be treated as an unforced Rule 30 history; see
the [independently verified XOR-rigidity audit and premise obstruction](../catalog-review/README.md#xor-rigidity-audit).

## A rejected full-row recovery horizon

The proposed implication from `2*n+2` equal observations of two `n`-bit
rows to an early stripe relation is false. Rows **33 and 45**, center index
**5**, both fit in six bits. Their observations agree at every time
`t < 58` and differ at time `58`. Neither the initial pair nor its first
step is stripe-related. These statements, including the negated early
relation, are proved in `Rule30TraceHorizonCounterexampleResearch.lean`.

The negative relation proof uses the all-time trace-preservation theorem:
an early stripe relation would contradict the checked difference at time 58.
It does not assume an unproved numerical-normalizer interpretation.

Both rows have the same highest bit, hence the same physical left edge.
The example therefore rejects the proposed full-row horizon without
refuting an edge-only bound or EdgeObservable.

All five proof modules passed full replay with the unchanged official checker
at `2f63afda261888e04ec57237290e723190914a1d`: **9 forcing-law declarations,
8 full-row counterexample declarations, 52 inverse-code declarations, and
9 edge-horizon obstruction declarations, and 72 seed-boundary declarations**,
with twenty-seven selected headlines and only standard axioms. See
[the complete reports](evidence/report.json).

## Rejected tighter edge horizons

The candidate `2*n+2` must be distinguished from two tempting tighter bounds.
`Rule30EdgeHorizonObstructionResearch.lean` proves that rows **77 and 56**,
both below `2^7`, have different highest black bits (`6` and `5`) yet equal
center observations at index `c=1` for every `t < 13`. They first differ at
`t=13`. Their physical left edges are `-5` and `-4` in this frame.

Consequently **neither `2*n-c` nor `2*n-1` observations suffice in general**:
both proposed horizons are 13 for this pair. This is an edge-only obstruction,
unlike the same-edge pair 33/45 above. It does not refute `2*n+2`, contradict
EdgeObservable, or settle a prize problem. The complete prefix, next difference,
and the two rejected universal bounds are kernel-checked.

## The single seed has no nontrivial stripe partner

`Rule30SeedBoundaryResearch.lean` proves an unbounded restriction on the
single-seed route. Define `SeedLow(a)` by bit zero being black and bits one
and two being equal. In low-to-high order, those three bits are `(1,0,0)` or
`(1,1,1)`. Every packed row `Phi^t(1)` lies in this class, for every time `t`.

`seedLow_stripe_trivial` proves that a stripe-related partner of **any** row
in this class is that same row. Both the row size and center index are
unrestricted. The proof uses the exact stripe grammar: after either of these
three-bit prefixes the tail parser is permanently dead. A two-bit eligible
cut would require unequal bits one and two; a one-bit cut fixes both entire
rows. The class is preserved by `Phi` because bit zero stays black while
bits one and two both flip.

For a hypothetical eventual period with onset `T` and positive period `P`,
the two rows must first be aligned to a common moving right frame:

```text
a = Phi^T(1) << P       b = Phi^(T+P)(1)       c = T+P.
```

Row `a` is even, and row `b` has `SeedLow`. `period_pair_never_stripe` proves
that their future rows cannot enter the stripe relation at **any** time or
center. Thus the known stripe ambiguity cannot explain a periodic seed trace.
This does not establish that the traces eventually differ: completeness or
another separation argument is still required.

The same module formalizes a more restricted sufficient condition:
`SeedLowEvenLeftSeparation`. It asks only about nonzero even rows `a`, rows
`b` with `SeedLow`, and a black bit of `b` beyond every black bit of `a`.
It asserts that these rows cannot share an entire center trace. **This
condition is OPEN.** It does not demand full-row recovery or address pairs
with the same left edge.

`periodic_center_forces_seed_even_collision` proves that any eventual seed
period, with arbitrary onset and positive period, supplies exactly such a
pair. Its packed/physical correspondence, shift alignment, and left-edge
witness are proved in the module. Consequently
`problem1_of_seedLow_even_left_separation` concludes the exact official
`Rule30Prize.Problem1` **conditional on that open hypothesis**. The hypothesis
has not been proved or supplied; this is not an unconditional prize solution.

Independent physical truth-table controls compare 2695 cells and 819 aligned
row pairs (1638 center observations). They check the coordinate interpretation,
not the open separation statement. See [the controls](seed-boundary-controls.json).

## Exact inverse codes, with the right prefix supplied

`Rule30InverseTraceResearch.lean` constructs a unique initial row below `2^n`
from these data: its bits at indices below `c`, and its center observations
at times `t` satisfying `c+t < n`. Both `n` and `c` are arbitrary. Indices run
from physical right to left in the moving integer frame; observation `t` is
bit `c+t` of `Phi^t(a)`.

The construction chooses the initial bits from low to high. If two rows agree
below index `i`, their bit-`i` XOR difference stays unchanged after every number
of steps (`bit_xor_phiRows`). Thus the next initial bit can be chosen to force
the next requested observation. `inversePrefix_realizes` proves every requested
observation, `inversePrefix_right` preserves the supplied right prefix, and
`inversePrefix_unique` proves uniqueness. `finite_trace_code_injective` gives
the corresponding injectivity statement.

This is a constructive finite-prefix form of left permutivity, the property
behind the kit's existing `Rule30Realization` construction. No historical
priority or new prize result is claimed for that underlying principle.

The right prefix is an **input**, not something recovered by the theorem.
Arbitrary finite target words are realized by finite prefixes, but a compatible
sequence of such prefixes need not have a finite nonzero support. The theorem
does not establish that the constructed bits eventually become zero, preserve
the highest black bit, or prove EdgeObservable. No new prize claim follows.

The inverse probe computes temporal profiles of successive bit positions using
packed prefix XORs, then checks its result against direct forward Rule 30 for
every tested case. Five controls include the exact finite aliases `2` and `3`
at `c=1`, and the delayed required bit at index `63` for target row `45`,
`c=5`, and right prefix `1` (observation time `58`).

The [gap probe](inverse-trace-gap-probe.json) reconstructs 527 cases through
4096 observations, including both orders of earlier different-edge witnesses
and 400 seeded random cases. It tests truncations at consecutive required
black bits, including the last tested zero tail. No counterexample to the
candidate edge horizon was found. The final zero tail is treated only as
finite agreement; it is never assumed to stay zero forever.

The [section probe](inverse-section-probe.json) examines the trace-preserving
operation that flips the initial rightmost bit at `c=1`. Its 15-bit truncation
is an involution on all 32768 inputs, with 200 prefix-consistency controls.
The numbers of distinct five-bit residual maps at prefix depths zero through
ten are `1, 2, 3, 7, 13, 25, 48, 92, 180, 351, 702`. These finite observations
do not prove infinite-state behavior or any computational lower bound. The
8192-observation sample tails also make no claim of permanent zero tails or
infinite nonperiodicity. These two Python experiments are not Lean proofs.

## Finite edge-recovery probe

The edge-only candidate tested was: for nonzero rows below `2^n` and center
index `0 <= c < n`, equality through `2*n+2` observations determines their
highest bit. This is an **unproved conjecture**.

The experiment enumerated every nonzero row for 69 selected `(n,c)` domains,
with `4 <= n <= 17` and up to five center indices per width. No counterexample
to that candidate was found. It does not test every center index or prove
an unbounded statement. The full report gives every domain and witness.

For each domain, all observed trace buckets are checked for conflicting
highest-bit labels. Sorting fixed-length trace words in observation order
then gives the longest common prefix across different labels by examining
adjacent label changes. This avoids enumerating every pair at large widths.
The algorithm is independently checked by a direct all-pairs calculation in
24 small domains, covering 142960 different-edge pairs. A physical
position-indexed Rule 30 truth table independently checks 640 observations,
including the 58-step witness. See [the control report](probe-controls.json).

The earlier full-recovery probe stops at a finite collision requiring more
than forty observations; it verifies that the pair separates by time 512.
Its unresolved finite collision is not an infinite-trace counterexample.
All experiment reports explicitly mark completeness and Problem 1 unproved.

The [two-limb vector probe](vector-edge-horizon-probe.json) subsequently
enumerated every nonzero row below `2^n` in **12 selected domains**: widths
20, 22, and 24, with four center indices per width. It computed **88080372
row traces**, each with 64 observations; no counterexample to `2*n+2` was found.
A [separate width-24, center-1 domain](vector-edge-c1-probe.json) enumerated
16777215 rows and also found none. This is selected-center coverage, not every
center at those widths and not an unbounded proof.

The NumPy implementation uses two unsigned 64-bit limbs. Truncation above bit
127 is safe for the observed indices because `Phi` at a given index depends
only on that index and lower indices. Before the large domains, 512 comparisons
with Python integer evolution exercise carries across the limb boundary;
independent direct checks cover 21076 small different-edge pairs. Every reported
maximal-delay witness is also checked by Python integers. The sorting argument
and domain guards are the same as above; a stopped domain is never listed as
complete. NumPy results are numerical evidence, not Lean proofs.

The [bounded solver search](solver-edge-horizon-probe.json) asks for a row with
highest bit 31 and a nonzero row with a smaller highest bit, at center index 8,
sharing the first 66 observations. Its result is **unknown (timeout)**, not
UNSAT and not evidence that this domain satisfies the candidate bound. The
solver model is independently checked on all 4032 pairs in a small domain
using physical truth-table evolution: 13 observations admit a collision there,
while 14 do not. No solver UNSAT result is used as a Lean premise.

## Finite ancestry: a bound and a failed short trace horizon

The separate [ancestry module](Rule30AncestryResearch.lean) proves, for every
nonzero natural row `a` and every time `t`,

```text
log2(Phi^t(a)) = log2(a) + 2*t.
```

Consequently any positive finite ancestor `b` satisfying `Phi^t(b)=a` has
`2*t <= log2(a)`. This is an elementary support calculation. It bounds the
possible finite prehistory; it does not recover that prehistory from a trace.

The same module refutes the attempted `2*n+2` horizon for recovering even
**finite-predecessor membership**. The rows `49` and `42` at center index `2`
agree at times `0` through `16`, then differ at time `17`. Both are six-bit
rows with highest black bit `5`. Row `49` has the finite predecessor `15`;
row `42` has no natural-number predecessor at all. That nonexistence is
proved for every natural input: the support theorem bounds any prospective
parent below `16`, and the remaining finite check is kernel checked.

Here `2*n+2=14`, so this is a counterexample to the short ancestry horizon.
The equal highest bits mean it is **not** a counterexample to the edge-only
candidate above. It also does not refute ancestry recovery from an entire
infinite trace. That proposed direction still needs an unbounded argument;
the finite experiments have not supplied one.

[The catalog bridge](Rule30AncestryCatalogBridge.lean) proves that the
lightweight module's update, iterates and observation predicate agree with
the adopted `Rule30StripeMeeting` constants, and states the counterexample
with those catalog constants. All **52 declarations and 12 selected
headlines** across the two modules passed full kernel replay at the updated
verifier commit `3eca23c0a9fa6b153313655e6d51835406c2d06e`, with the unchanged
checker and standard axioms only. See [the report](evidence/ancestry-3eca/report.json).
The earlier five-module reports remain pinned to their original commit.

Independent physical-coordinate Rule 30 truth-table controls compare 828
cells, reproduce the first distinguishing time, and check 64 one-step parent
examples. Their finite checks do not establish the unbounded no-parent
statement; the Lean support argument does that. See [the controls](ancestry-controls.json).

```text
python research/trace-completeness/verify_ancestry.py --project /path/to/3eca23c-kit --lake /path/to/lake
python research/trace-completeness/control_ancestry.py
```

## Reproduce the earlier packages

Prepare the reference kit and first run the twelve-module
[`normalization-first-meeting/replay.py`](../normalization-first-meeting/replay.py)
against it. This supplies the exact semantic proof dependencies. Then run:

```text
python research/trace-completeness/verify.py --project /path/to/pinned-kit --lake /path/to/lake
python research/trace-completeness/trace_completeness_width_probe.py
python research/trace-completeness/edge_completeness_width_probe.py
python research/trace-completeness/control_probes.py
python research/trace-completeness/inverse_trace_gap_probe.py
python research/trace-completeness/inverse_section_probe.py
python research/trace-completeness/vector_edge_horizon_probe.py
python research/trace-completeness/vector_edge_horizon_probe.py --widths 24 --centers 1 --output research/trace-completeness/vector-edge-c1-probe.json
python research/trace-completeness/solver_edge_horizon_probe.py
python research/trace-completeness/control_seed_boundary.py
```

The proof runner checks prerequisite source hashes and the original checker,
guards every owned compiler/replay process, and freshly replays all five modules.
The enumeration and gap probes have separate time and memory guards and report
partial scope on interruption. The section probe uses the fixed workloads
described above. Logs and Python caches are ignored.
The vector probe requires NumPy; the optional bounded solver probe requires
`z3-solver`. The saved runs used NumPy 1.26.4 and Z3 5.3.1. The solver has a
45-second default timeout and a 1536 MB internal memory limit; its saved run
also used the compiler runner's external time and memory guard.
