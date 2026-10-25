# Actual return-depth cancellation and an information-losing echo profile

Troy Lowry and Codex, 25 October 2026. **Prize Problem 1 remains open.**
This work strengthens the [complete source bridge](../20261025-source-green/REPORT.md)
using the actual seed return word, and tests a proposed recursion for the
remaining channels. It does not claim an uncancelled full source sum.

## The actual least-unreturned bit

Let R(d,t)=cell(t,t-d), and for H>0 define rho(H) as the least d with
R(d,H) different from R(d,0). This is a defined quantity of the actual seed
orbit, not an assumed invariant. The second black cell at the moving left
edge proves existence and `0<rho(H)<=2H-1`.

[ReturnDepth](work/Rule30ReturnDepthResearch.lean) proves for every H>0:

- Every bit below rho has period H for all future times.
- Bit rho flips after H steps, for every future time.
- At time H-1 all lower bits are black and bit rho is white.
- The run-boundary source at depth rho is zero at H-1 and is one at
  H+v whenever 2v+1<rho.

These are full, actual-seed statements. The period of the returned prefix
is obtained from its exact return and the triangular Rule30 recurrence;
it is not inferred from a finite observed prefix.

## A stronger complete-source cutoff, and the first interior cancellation

Put H=2^e, n=2H-1, m=n-1. Use the previous actual run-boundary source
b(d,s)=cell(s,s-d) AND NOT cell(s,s-d+1), including b(0,s)=1, and weight

```
W(e,s,d) = b(d,s) * [if 2 divides m-d then choose(m-s,(m-d)/2) mod 2 else 0].
```

All equations below are over GF(2). [ReturnSources](work/Rule30ReturnSourcesResearch.lean)
proves that the only nonzero mask-selected source at depths d<rho(H) is
the outer source d=0,s=H-1. It also proves `e<rho(2^e)`, so the new cutoff
is at least as strong as the earlier logarithmic strip.

[ReturnSum](work/Rule30ReturnSumResearch.lean) connects this to the full,
kernel-checked Duhamel expansion:

```
c(2H-1) = 1 + sum(s<n) sum(rho(H)<=d<n) W(e,s,d).
```

The new [FirstReturnParity](work/Rule30FirstReturnParityResearch.lean)
proves the previously tested leading-channel prediction uniformly:
**if the actual rho(H)=2r is even, its entire channel has parity one.**
Pointwise source phases reduce its sum to a finite binomial interval;
the hockey-stick identity and Lucas' all-ones case evaluate it to 1.
Consequently the outer 1 and this first interior channel cancel exactly:

```
if rho(H) is even:
c(2H-1) = sum(s<n) sum(rho(H)<d<n) W(e,s,d).
```

This is a localization and cancellation theorem, not a noncancellation
theorem. It explains why finding the first odd interior channel does not
solve the problem. The complete higher remainder is unrestricted. No claim
that rho is even infinitely often has been proved or used. For odd rho,
rounding it up to the next even depth remains invalid (the preceding H=16,
rho=7 example first becomes active at depth 14 and odd at depth 18).

The proof counts are ReturnDepth 46, ReturnSources 31, ReturnSum 13,
FirstReturnParity 29 and EchoProjection 36: **155 newly replayed constants**,
including generated declarations. All five modules passed full replay and
every selected headline with the unchanged official checker, standard
axioms only, no new axioms, and the same verifier pin 3eca. The final source
build logs are empty. Existing proof dependencies were reused unchanged
from the preceding checked archive; their exact sources and reports are
also carried here. This does not count them again as new results.

## Why the proposed echo recursion needs more state

For a finite right-edge row a, let Phi(a)=a XOR ((a<<1) OR (a<<2)), let
Delta f=f composed with Phi + f, and write a_j for bit j. The proposed
source channel and its cumulative echo are

```
C_r(a) = Delta^r b_(2r)(a),
G_r(a) = Delta^r a_(2r-1)  (r>0), G_0=0.
```

The local source identity gives the algebraic telescoping
`C_r=G_(r+1)+G_r`. Direct submask sums independently checked this in
10,752 cases. At dyadic H, taking a=Phi^(H-1)(1) makes the full channel sum
equal the actual c(2H-1). Thus telescoping alone supplies another encoding
of the same final parity, not an independent bound on it. The G identity
is a derivation and finite control here, not a separately claimed Lean result.

[EchoProjection](work/Rule30EchoProjectionResearch.lean) proves a stronger
obstruction to using C as an autonomous state. Define the entire infinite
profile at canonical phase t by the XOR of b(2r,t+u) over submasks u of r.
The profiles at t=0 and t=1 are exactly equal for every r: depth zero is
one and every positive channel is zero. But the next profiles differ,
already at channel r=2 at t=2. Hence **no deterministic function of this
entire profile alone advances all canonical phases by one step.** The
theorem quantifies over arbitrary functions, not just fitted finite readers.
Its all-depth part uses the known left-edge diagonals, including D2=0
from time 2; the small next-channel fact is checked with `decide +kernel`.
Adding a clock, history, another field, or a different representation is
not ruled out. No general machine or computation lower bound is claimed.

Two quick simplification attempts also failed:

- The proposed G_r=1 beyond r>=2*width+2 fails even on the canonical seed
  row Phi^2(1)=25, width 5: G_12=0. A generic SeedLow witness is row 9,
  width 4, at r=10. Finite tail statistics are not infinite-tail theorems.
- Exact symbolic truth tables on finite prefixes give rapidly growing
  Boolean degrees. With the highest readout input fixed zero, r=2..9 gives
  degrees 2,4,6,8,10,12,14,16. On the SeedLow restriction the degrees are
  0,2,3,6,7,10,11,14. Every selected top-degree coefficient was independently
  checked by direct-evolution Mobius parity, and 1,490 direct truth-table
  controls passed. These are finite ANFs, not an unbounded-degree theorem,
  and high degree does not exclude a nonlinear recursive algorithm.

## Validation and limits

Independent controls compared 4,420 physical cells, 33,024 returned-prefix
observations, 33,024 cut-bit flips, 250 source-window observations, 2,047
all-ones binomial coefficients, 22,992 mask events below the actual cut and
788 direct binomial terms in the leading channel. The complete source sums
and the leading-cancellation examples agree with the actual seed center.

All eight final jobs exited normally under the owned 300-second/8-GiB-RSS/
2-GiB-system-free guard. The largest job used about 2.16 GiB owned RSS;
the final leading-parity replay took 42.875 seconds. Existing checker
deprecation output is preserved. No other session files, processes or
actual computer configuration were changed; GPU and G913 were unused.

The 16:51 UTC public refresh still has 41 entries, no new/removed/changed
entry fields, and verifier/upstream main at 3eca. No new public proof was
adopted. Existing catalog PR23 is still open at the same head, without a
review decision or GitHub status checks. This batch makes no new PR, prize
essay or API submission. The earlier core contribution remains the
[catalog PR23](../20261025-source-catalog/REPORT.md).

The full goal stays active. The next argument must constrain the complete
higher-source remainder or use a representation retaining the needed
state; another leading odd source or a reader of this profile alone is
insufficient. No step here proves or disproves official Problem1.
