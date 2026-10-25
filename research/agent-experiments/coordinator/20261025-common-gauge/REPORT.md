# Common-gauge sparse observer experiment

This is finite exploratory work. It is not Lean verified and does not solve
Rule 30 Prize Problem 1 or prove unbounded observability.

## Exact constraints tested

Let A and B be actual Rule 30 trajectories, and let delta = A XOR B.
The common candidate field h is required to satisfy the frozen linear equation

    h(t+1,p) + h(t,p-1) + (1+B(t,p+1))*h(t,p)
        + (1+A(t,p))*h(t,p+1) = 0

and, in the joint experiment, the additional local wedge constraint

    delta(t,p+1)*h(t,p) + delta(t,p)*h(t,p+1) = 0.

Arithmetic is over F2. The second constraint is the difference between the two
local divided-difference gauges applied to the SAME field. The actual difference
delta satisfies both constraints. An arbitrary auxiliary solution of just one
gauge does not have to satisfy the second constraint. This experiment does not
identify independent gauge evolutions with a common field.

The observation assumption is h(t,0)=0 through N. The initial source support is
[-U,U]. Equations are restricted to the backward sensor cone and intersected
with the forward source cone; variables outside the latter are known zero.
The target is h(0,-U). Sparse elimination contracts one-variable equations to
zero and two-variable equations to equalities, repeatedly reducing all rows.

## Results

* Degree-one peeling of a single gauge fails already at canonical times U=4,
  V=0 through N=48. Dense elimination nevertheless recovers the source unit
  through time 8, with observation times [1,2,4,8]. The failure is a limitation
  of peeling, not a counterexample to observability.
* Adding two-variable equality contraction to one gauge first fails in the
  ordered tested range at U=9,V=1,N=68. Dense elimination recovers the source
  unit through time 12 using [6,10,12].
* Adding the wedge constraints succeeds for all 300 canonical pairs
  1<=U<=24, 0<=V<U, at N=4U+32. Each tested physical local equation and wedge
  identity is checked against independently evolved actual differences.
* The joint run took 21.578 seconds, with 24.8 MB sampled peak owned RSS under
  the ordinary 300 second/8 GiB/2 GiB-free guard. No guard fired.

These positive finite cases do not give a termination argument at arbitrary
U,V. They motivated the independently checked certificates and scope tests
below. No new Lean theorem is claimed in this checkpoint.

## Independent certificates, including the shorter deadline

Weighted union-find now records an exact XOR combination of the original
equation rows for every recovered source unit. A separate verifier imports
none of that producer: it evolves Rule 30 as sets of integer positions and
reconstructs each selected equation as a set of spacetime coordinates. It
checks that the XOR of the selected equations is exactly the initial left
source, and that the selected observations have actual parity one.

The initial 300 certificates passed. A specific attempted falsification of
the short deadline N=U then passed for all 820 canonical pairs
1<=U<=40, 0<=V<U. Their derivations were also serialized and independently
checked. Across the two datasets there are **1,120 certificates for 820
distinct pairs**, not 1,120 distinct pairs. No uniform deadline is proved.

The independent verifier also passed 11 controls, replayed 235,841 selected
physical identities, and rejected 1,123 corrupted positive certificates
(1,120 canonical and three later-recovery controls). Each corruption toggles
the time-zero observation, changing the combined coordinate row. Five Rule
210 comparisons produce no source-unit certificate because their actual
center differences remain zero throughout the tested windows. The pinned
catalog already proves the relevant all-time fact as
[`Rule30Realization.center210`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/0090056412733accaa27643d3cbbf982104f2251/lean/Ruliology/CellularAutomata/Rule30Realization.lean).
That fact is existing work, not a new result here.

The finite N=U phenomenon should not be read as evidence that the unbounded
step is nearly complete: ordinary finite trace separation is easy to observe
in these cases. The missing result is a reason that covers every U,V.

## An exact obstruction to weakening the history assumption

Keeping A equal to canonical time U but replacing B by another finite start
can destroy the N=U bound. Three concrete controls make the scope precise:

| U | Replacement B | Conditions retained | Matching trace through | First disagreement |
|---|---|---|---|---|
| 2 | black only at +1 | smaller support radius | 2 | 3 |
| 4 | black at -3,0,2,3 | centered bounding edges -3,+3 | 4 | 6 |
| 11 | black at -6,-5,-2,-1,1,5,6 | centered bounding edges -6,+6 and four canonical left-edge cells at time 6 | 11 | 12 |

The last pair has A black at
`-11,-10,-8,-7,-6,-5,-2,-1,1,6,8,9,10,11`.
Its common center prefix through time 11 is `001011001001`.
The four preserved B cells, from positions -6 to -3, are `1100`.
B is not a time-6 single-seed row. The actual physical difference itself is
a nonzero-left-source, zero-observation witness through N=U. Thus **no sound
linear elimination can establish that deadline for these weakened classes**;
this is stronger than a failure of one sparse algorithm.

These are finite collisions. They do not refute eventual separation, the
original canonical deadline conjecture, EdgeObservable, or Problem 1. A
larger deadline for wider classes also remains possible.

The efficient search uses left-permutivity. A candidate initial right half
and a prescribed center trace determine the necessary initial left half.
Integer bit planes evaluate all candidate right halves at once, then filter
by the required left support and prefix. A wholly separate scalar verifier
enumerates full initial configurations: it matched all 57 inverse-circuit
cases and both centered collisions, checking 14,764 initial words. The
inverse method reproduced the small direct search and found the four-cell
collision at U=11, just beyond that direct search's U<=10 cap.

An early diagnostic wrapper incorrectly asserted that a collision had to
occur inside that smaller cap. Its failed source/log/guard are retained as
`work/evidence/attempt01-assumed-counter`. The corrected result distinguishes
no collision within a cap from a theorem. No failing run is counted as a pass.

## Public refresh

The reference pin is still 0090056412733accaa27643d3cbbf982104f2251.
There are no newly listed submissions relative to the preceding saved refresh.
One existing abstract was expanded: R30-20261025-017d83 describes unconditional
four- and five-cell stripe-tail mortality. Its public source was downloaded and
the named results are present; the verifier reports those four headlines passed
at 2026-10-25T09:59:56Z. No external theorem was newly adopted in this experiment.

## Next work

The certificate serialization and independent replay are complete at the
finite scope above. The attempted support-only and four-cell-prefix shortcuts
to the N=U deadline are refuted. The next argument must retain more of the
relationship between the two canonical trajectories, or prove a different
unbounded criterion. Increasing either census is not that argument.

In particular, certificates may use wedge identities outside the very short
causal path from the source to an observation. The common-field constraints
are stronger than a single frozen linear evolution. Their success does not
prove single-gauge observability. The original observer conjectures and P1
remain open.

The essay notebook memory-wait helper is separate. Its unfinished fresh replay
is not a mathematical blocker and is not counted as a successful validation.
