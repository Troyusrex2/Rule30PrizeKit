# A true mismatch birth in every padded doubling block

Complete paper proof from the verified physical episode theorem and the
official MaskedJen window theorem. No new build or numerical control was
used. Root supplied the stronger block refinement below, improving the
initial separated-window argument and removing explicit episode counting.

## Fixed parameters and exact event

Assume the actual single-seed physical center c(t)=cell t 0 is P-periodic
from T, with P>0. Choose ONCE

    Q=2P,
    n0>=T+Q,
    n0>=2Q.

All these choices precede every horizon quantifier. Write

    delta_Q(t)=cell(t,1) XOR cell(t-Q,1),
    trueBirth_Q(t)=(NOT delta_Q(t)) AND delta_Q(t+1),
    birthCount(Q,n0,X)=sum_(n0<=t<X-1) trueBirth_Q(t).

The sum is an ordinary nonnegative integer count over the half-open source
interval[n0,X-1), with the usual empty-interval convention. For valid tail
times the checked true_birth_iff identifies this event exactly with

    cell(t,1)=cell(t-Q,1)=0,
    cell(t,2) != cell(t-Q,2).

This is a literal physical Q-shift, not a same-index sheared-column shift.

## One true birth in one block

Fix n>=T+Q. The checked bounded_mismatch_episode theorem, applied at n,
gives a time z with

    n<=z<=n+Q,    delta_Q(z)=0.

The center is Q-periodic from T because P divides Q. The official
Rule30MaskedJen.periodic_window theorem applied at N=n+Q gives

    n+Q<=s<2(n+Q),
    c(s)=0,    delta_Q(s)=1.

Its upper endpoint is STRICT. Its onset requirement T+Q<=N holds because
n>=T+Q. Thus z<=s, and their different bits force z<s.

For any Boolean stream, a zero at z followed by a one at s has a true
zero-to-one transition between them. For example, choose the first one
after z; its predecessor u satisfies

    z<=u<s,
    delta_Q(u)=0,    delta_Q(u+1)=1.

Therefore this ACTUAL birth satisfies

    n<=u,    u+1<=s<2(n+Q).                            (B1)

In particular u<2(n+Q)-1. No persistent source is counted again merely
because it is read repeatedly, and no claim about an arbitrary driver is
used. The conclusion follows from the actual finite-seed window theorem.

## Iterate disjoint blocks

Define b0=n0 and b_(k+1)=2(b_k+Q). By induction,

    b_k+2Q=2^k(n0+2Q),                                (B2)

and every b_k>=n0>=T+Q. Apply(B1) to each b_k. The resulting birth lies
in[b_k,b_(k+1)), strictly before its last source tick. These intervals are
disjoint, so for every k,

    k <= sum_(n0<=t<b_k) trueBirth_Q(t).                (B3)

This also follows directly by induction with intervalCount_split; no
formal definition of maximal episodes or quotient by episodes is needed.

For m>=1 set k=2m-1. Since n0>=2Q, (B2) gives

    b_k+2Q
      =2^(2m-1)(n0+2Q)
      <=2^(2m-1)*(2n0)
      =4^m*n0.

Because Q>=2, b_k<=4^m*n0-1. Thus the count in(B3) is contained in the
source interval defining birthCount(Q,n0,4^m*n0), and

    2m <= birthCount(Q,n0,4^m*n0)+1.                   (B4)

For m=0, the left side is zero and the inequality is immediate, including
the empty source interval[n0,n0-1). This handles all natural m without
using truncated subtraction in the theorem's lower bound.

## A weaker sufficient upper-frequency obligation

The earlier episode estimate N_Q(X)<=H_Q*(initial episode+birth count)
would require a birth upper slope of roughly1/H_Q to reach the chosen
masked-defect budget. The direct birth lower bound(B4) instead proves the
following sufficient criterion for the OFFICIAL Problem1:

For every hypothetical center period(T,P), choose n0,C,M with

    n0>=T+2P, n0>=4P,
    for all m>=M,
      birthCount(2P,n0,4^m*n0)<=C+m.                   (B5)

All choices are fixed before m. At m=M+C+2, (B4) and(B5) give

    2m<=C+m+1,

which implies m<=C+1 and contradicts the chosen m. Thus(B5) would exclude
every eventual center period. The upper-frequency estimate(B5) is NOT
proved here; this package proves the stronger lower bound and its precise
conditional consequence, not Problem1.

The argument uses no unproved center-to-sheared-column identification,
no whole-prefix return, no larger clock enumeration and no horizon-dependent
Q. It exploits the actual finite-seed quantitative window theorem together
with the new coherent-shift residence bound.
