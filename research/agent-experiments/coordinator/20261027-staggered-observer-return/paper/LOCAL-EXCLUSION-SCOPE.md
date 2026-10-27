# The depth-two exclusion needs no whole-output clock

Separate scope strengthening of the frozen DEPTH-TWO-EXCLUSION.md,
SHA8440c7f753a96ad17e034462d554d7e962588e3cc4feb89e2b6bfa25fa3e0e58.
That file is not edited. This note is a complete paper argument, not a
claim of an additional successful Lean replay.

## A local actual-strip assertion

Let P>0 be even. Let x0,...,x7 be actual profiles on Nat, with the literal
overlapping recurrence for indices0 through5:

    x_i(t+1)=x_i(t) XOR (x_(i+1)(t) OR x_(i+2)(t)).

Assume x2 is anti-P and x3 is P-periodic, for all times. Put

    h0(t)=x0(t+P)+x0(t),
    h1(t)=x1(t+P)+x1(t),

where + means XOR, and E(t)=1 on even times. Then

    NOT(for all t, h0(t)=E(t)*h1(t)).                  (L0)

No period of x0 or x1 is assumed. The two oldest profiles x6,x7 may be free
drivers; their shared use in the recurrences of x4,x5 is retained. Thus
this is a genuine local exclusion, not a theorem whose missing boundary
hypothesis is concealed. Finite-white histories satisfy these local
recurrences as a special case.

## The algebra does not require a smaller whole clock

Use the frozen proof's notation z=x2,f=x3,g=x4,k=x5,l=x6,m=x7,
a=f OR g, y=h1, r=x1+z*y, O=1+E. The actual anti-period and old period give

    Delta y=1+f;
    Delta r=f+a*y^+;
    Delta h0=1+r.

For clarity, the middle identity follows by expanding x1'=x1+z+f+zf
and (z+a)(y+1+f); the z and zf terms cancel. The last identity follows
directly by subtracting the OR drivers of x0 and its P-shift. Neither
identity assumes that y or r is P-periodic.

Under the proposed boundary h0=E*y, the same calculation as in the frozen
proof yields

    E*Delta f=f+a*y^+.

Put q=y+O. Then Delta q=f. The local identities imply

    g*q=0;
    at an odd tick, q=1 implies q^+=1.                 (L1)

These are exactly(D6),(D7) in the frozen proof, with the same derivations.

## Forward propagation replaces every periodicity use

If q=1 at an odd tick t, it is one at t+1 by(L1). Thus g(t)=g(t+1)=0.
The ACTUAL relation Delta g=k OR l gives k(t)=l(t)=0, so
Delta f(t)=g(t) OR k(t)=0. Since f(t)=q(t)+q(t+1)=0, also f(t+1)=0,
and q(t+2)=1. Induction propagates this to EVERY time at or after t.

On that future tail q=1 makes f=Delta q=0 and g=0, so a=0. But z'=z+a
would make z eventually constant, contradicting its all-time anti-P law.
Hence q is zero at every odd time, without any whole-clock premise.

It follows that g=k=0 at odd ticks. At each even tick t>=2, the previous
odd tick and the actual recurrences give g(t)<=k(t), while the next odd
tick gives g(t)=k(t) OR l(t)>=k(t). Thus

    g(t)=k(t) for every t>=1.                          (L2)

The marked time0 is not forced into this equality and is not needed.

At any even t>=2 with q(t)=1, (L1),(L2) give g(t)=k(t)=0. Therefore
Delta f(t)=0, and the identities f(t)=q(t), f(t+1)=q(t+2) propagate
q(t+2)=1. Two cases now exhaust the possible future:

* Some even t>=2 has q(t)=1. Then q=E at every sufficiently late time.
* No even t>=2 has q(t)=1. Then q=0 at every time>=2.

Accordingly f=Delta q is eventually constant1 or constant0. In both
cases Delta f=0 eventually, so g=k=0 eventually. Thus a=f OR g is
eventually a constant bit c.

Choose any s beyond that onset. Repeating z'=z+c exactly P times gives
z(s+P)=z(s), because P is even. This contradicts z(s+P)=1+z(s).
The contradiction proves(L0). No entire-output clock, finite support,
least period, or time0 wrap was used.

## Consequence for an actual finite word

Suppose an older actual prefix returns after a positive even P and at
most three newer coordinates are appended. If the full word failed to
return at P, choose its oldest failing coordinate. Triangular autonomy
makes its P-shift defect the constant one and all older defects zero.

If that coordinate is the newest or penultimate, the two short cases in
the frozen proof give the contradiction directly. If it is the third
newest, its trace is anti-P and the next older trace is P-periodic, so(L0)
applies. Therefore the defect boundary alone forces whole return at P.

Full all-time gates imply that defect boundary because P is even. This
gives the direct three-cell gated extension result without an auxiliary
8P return bound or repeated halving. The arbitrary-width transfer remains
open: the local proof still needs the unit birth within three coordinates.
