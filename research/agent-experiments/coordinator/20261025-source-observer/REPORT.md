# Exact multi-output observers: a research lead, not a prize proof

**Problem 1 remains open. No new Lean theorem, complete solution or prize
submission is claimed in this checkpoint.** These are finite computations
with independently checked algebraic certificates. The earlier uniform
[delayed-period theorem](../20261025-delayed-periods/REPORT.md) and
[PR25](https://github.com/WolframInstitute/Rule30PrizeKit/pull/25) remain the
latest proved contribution.

## The exact question

For two actual evolutions A and B, put d=A XOR B. The Rule30 identity is

    d(t+1,p) = d(t,p-1)
               XOR ((1 XOR B(t,p+1)) AND d(t,p))
               XOR ((1 XOR A(t,p)) AND d(t,p+1)).

Once A and B are fixed, this is a linear equation over F2 for d. The local
identity was checked on all 64 paired neighborhoods; the Rule210 control
identity was also checked on all 64. The coefficient of the center term for
Rule210 is B(t,p+1), without the extra 1. This distinction is essential.

Take A initially at canonical time U, B at canonical time V, U>V>=0.
Both are supported in [-U,U]. Their initial difference is 1 at -U. Propagate
every source basis vector through the frozen linear coefficient field, and
let v(t) be its row of coefficients at the center. Seek finitely many times
S such that XOR over t in S of v(t) is the unit vector at -U. If found,

    XOR over t in S of (center(U+t) XOR center(V+t)) = 1.

This is a multi-output source certificate, not a claim that one ancestry
path survives cancellation. The initial source outside [-U,U] is known zero.
**If such a certificate were proved to exist for every U>V, Problem1 would
follow:** choose U=T+P and V=T in any proposed eventual period. That universal
existence theorem is missing. A stronger certificate criterion must not be
confused with the actual trace-separation question it would suffice to solve.
The kit's related `Rule30TraceEdge.EdgeObservable` is also an open hypothesis.

## Finite evidence and limits

- All 548 basic canonical pairs recovered the edge unit: U<=32 with every
  V<U, plus five V choices at U=48,64,96,128.
- All 33 completed stress cases recovered it, through U=4096. Ten overlap
  the basic set, giving **571 distinct canonical pairs**, not 581. The stress
  job stopped normally at its internal time budget; two additional planned
  U=4096 cases were never started.
- All 2,300 seeded random finite-background pairs recovered it.
- All 69,904 exhaustive small pairs (U=1..4) and 11,236 structured periodic
  truncation pairs recovered it. These are bounded experiments, not uniform
  finite-configuration theorems. Only exceptional records were saved by that
  search; its counts and exact generator are retained.
- Of 36 Rule210 controls, only four recovered within their caps. The other
  32 are capped non-recoveries, not new all-time impossibility proofs.

The [independent verifier](work/verify_observers.py) does not propagate a
forward basis field or perform Gaussian elimination. It propagates each
saved certificate backward with the adjoint operator and checks that its
initial row is exactly the edge unit on the known source interval. It checks
the actual output parity separately. It validated **2,891 certificate records**
(including four Rule210 controls and six solver-generated examples), and
rejected 2,891 deliberately altered time-zero certificates. The artifact
verifier reruns these checks directly without trusting the saved verdict.
All of these are Python checks; none is advertised as a Lean kernel replay.

## An explicit failed deadline estimate

The solver searches for an auxiliary initial linear mode h whose leftmost
bit is 1 but whose center outputs are all zero through a chosen horizon.
A checked h certifies that the edge unit is not in the observation row span
at that horizon. It need not equal the actual difference A XOR B.

For U=6, source positions -6..6 encoded from least to most significant bit,

    A = 0x1d2b, B = 0x978, h = 0x503

gives zero auxiliary center outputs for every time 0..20. It refutes a
generic deadline of 2*U+8. The edge unit is recovered at time 23 instead.
**The actual A/B center traces already differ at time zero.** This example
is about the stronger observer's latency and does not show delayed actual
trace separation, a canonical counterexample, or failure at every horizon.
Six SAT witnesses passed independent integer checks; three other solver
queries timed out. A timeout establishes neither existence nor nonexistence.

## A separate profile shortcut failed

The proposed even/odd pairing C(r,2t)=C(r,2t+1) for the complete canonical
echo profile is false: r=3 gives C(3,4)=0 and C(3,5)=1. The profile script
also has 1,089 independent finite-difference/submask controls. Absence of
aliases in a finite clock-augmented sample does not prove autonomous closure.

## What would count as progress next

Construct the observer for arbitrary canonical U,V, or prove a weaker
non-cancellation statement for the actual initial difference. Alternatively,
find a rigorously justified all-time obstruction to this stronger linear
criterion so it can be discarded. More finite successes alone do neither.
The exact coefficient fields, cancellation, finite source interval and
Rule210 control must all be retained in a proposed proof.

The public submissions snapshot contained 41 entries and no new or changed
entry relative to the previous check. The verifier pin was still
0090056412733accaa27643d3cbbf982104f2251. No external unverified result was
adopted. All seven jobs terminated normally under the saved 300-second,
8-GiB owned-memory, 2-GiB minimum-available-memory guards. No computer settings
were changed, no new prize essay was submitted, and no new PR was opened.
