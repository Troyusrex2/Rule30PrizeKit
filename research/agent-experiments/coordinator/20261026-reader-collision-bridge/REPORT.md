# The reader's accepted states supply the collision clock

Problem 1 remains open. This checkpoint removes one formerly independent
gap from the current plan: **separation in reader state 15 would imply the
collision-clock condition and, with finite initial difference, initial-subset
preservation.** It does not prove that separation or the fixed-center bridge.

## Unconditional part

Use the existing one-sided marching coordinates, with a white boundary:
`a(t+1,j+2) = a(t,j+2) XOR (a(t,j+1) OR a(t,j))` and the corresponding
boundary rules at 0 and 1. Write `d(t,j) = a(t,j) XOR b(t,j)`.
The reader scans paired initial bits from that boundary toward larger depth.

For every width `n+2`, if the initial prefix is accepted by the sound
17-state reader, then:

- In states 0, 3 or 12, `d(t,n+2) = d(0,n+2)` for every time `t`
  (`non16_permanent`). The preceding adjacent OR profiles agree forever,
  so the next difference never changes.
- In state 16, `a(t+1,n+1) = NOT a(t,n+1)` and
  `d(t+2,n) = d(t,n)` for every `t` (`sixteen_clock`).

Consequently, if `d(0,n+2)=1`, either this source stays opposite forever,
or the shared neighboring column alternates and the earlier difference has
period two. This is `accepted_collision_clock`, an all-width, all-time
theorem, without a supplied collision-clock hypothesis.

The proof reuses the 47-state coupled certificate and the reader's proved
period-two phase factor. A new finite kernel check verifies the two local
facts above. Induction on actual time makes them uniform. The state-16
predecessors force both OR inputs to 1; their difference is a function of
the reader state, whose two-step phase is the identity.

## The remaining premise is explicit

`SinkSeparates a b` says that every nonempty prefix whose initial reader
state is 15 eventually has unequal last-column bits. It is a definition of
an open hypothesis, not an axiom and not an asserted result.

Together with the existing nonsink completeness theorem, that premise gives
the full reader equivalence (`reader_exact_of_sink_separation`). In
particular, an all-time equal prefix cannot be in the sink and must be
accepted. Applying the unconditional result above gives
`collision_clock_of_sink_separation`.

The existing first-source argument then gives `front_of_sink_separation`
and `preservation_of_sink_separation`. The latter additionally requires
finite support of `d(0,.)`, exactly as the earlier preservation reduction
did. It does not require a new assumption of all-time subset preservation.

Earlier checkpoint language saying that complete reader separation would
*still* leave CollisionClock as an independent gap is superseded by this
proof. The fixed-center past observation remains a separate gap. Fixed
marching depth is a moving physical ray, not the vertical center column.

## Kernel checks and independent controls

[Rule30ReaderCollisionBridgeResearch.lean](work/Rule30ReaderCollisionBridgeResearch.lean)
has SHA-256 `09bbb9147e87b58b74e7b7816a8ee319a99135c52728ef0f1ea67bedd8735f6b`.
The unchanged official checker at kit commit
`0090056412733accaa27643d3cbbf982104f2251` replays all 47 declarations
and accepts all seven headlines with no new axioms. These are declarations,
including generated ones, not 47 claimed theorems. The new module's guarded
build and replay take about 1.85 seconds with peak owned RSS 780 MB on G913.
All four imported research modules were freshly rebuilt and fully replayed
in dependency order: 100, 81, 119 and 18 declarations pass respectively.
Their sources are byte-identical to the previously published proofs.

An independent literal Rule 30 truth-table implementation checks 3,029,216
cells. Exhaustive paired prefixes of widths 2 through 8 include 1,832
accepted pairs: 1,384 non-16 pairs and 448 state-16 pairs. All permanent and
clock checks pass, including 2,768 unequal next-bit extensions. A negative
control shows that state 16 cannot be silently treated as the permanent
case: prefix integers 1 and 2 at width 3, extended to 1 and 10 at width 4,
lose their next difference at time 1.

The local Wolfram Engine's built-in `CellularAutomaton[30]` independently
passes five controls covering all four accepted states and the nonpermanent
extension. Its arrays contain 910 sampled marching cells inside valid
causal cones. This is local software validation, not Wolfram backend or
human verification. No new essay or API submission was made.

## Invariant experiments: no certificate found

The accompanying `work/invariant-search/` contains the earlier attempts to
cover every temporal clock and every spatial width with one finite invariant.
For a time-word leaf `(uA,vA,uB,vB)`, spatial extension outputs
`(vA,wA,vB,wB)` and updates carries by `w ^= u OR v`. Cyclic closure is
required; the reader tag advances by the initial carry pair. The white seed
is the all-zero word. A bad profile has tag 15 and equal current columns.

Six ICE/SAT searches were tried: ordinary word automata, an exact safety
product, arbitrary binary trees, perfect dyadic trees, symmetry breaking,
and separate types for individual leaves versus larger dyadic blocks.
All failed to produce an inductive certificate within their stated caps.
State-bounded UNSAT, interrupted SAT solving, failed closure and incomplete
verification are retained distinctly. The last typed candidate has no
reported counterexample in its final partial check, but that check hit its
time limit and **does not count as a pass**.

An independent scalar audit validates every accumulated positive, negative
and implication fact from all six searches, plus 7,184 cyclic extension
edges and 17,328 rejected noncyclic carries. This validates the search data;
it does not prove that an invariant exists or that no such invariant exists.

An exact backward-language experiment, using no widening or learned guesses,
grows from 2 initial states to minimized automata of 7, 129 and 12,306 states
after one, two and three spatial preimage steps. The next composition hits
its explicit 100,000-state cap. All three preserve every nonempty white
seed length, and each agrees with all 6,128 reachable profile controls at
clocks 2, 4, 8 and 16. A separate literal unrolling audit passes 31,056 cases,
including nondyadic clocks. No fixed point is found; this is Python evidence,
not a Lean result or a lower bound on every possible invariant representation.

All jobs are terminal. Original outer guards remain 300 seconds, 8 GiB
owned RSS and 2 GiB minimum system available memory. See [reproduction
instructions](REPRODUCE.md), full formal reports, logs and manifests.

## Next target

Retain the white boundary and prove sink separation, or produce an actual
finite-prefix all-time collision in state 15. The new bridge makes that
target stronger: a proof also supplies the previously missing collision
clock and initial-subset preservation. A boundary-aware recursive witness
or a more structured invariant remains possible. No uniform finite-state
bound, full reader completeness, unconditional preservation or prize
solution is claimed.
