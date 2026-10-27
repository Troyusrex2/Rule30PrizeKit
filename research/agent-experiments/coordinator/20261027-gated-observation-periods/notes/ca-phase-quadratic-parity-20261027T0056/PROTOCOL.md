# A phase-sensitive quadratic cycle sum

Paper candidate, recorded before calculation. No Lean claim or public write.

Use the actual canonical finite words `100x`, with nonempty older-first tail x,
and T=C after A. Let r(t) be the newest bit of T^t x and s(t) its bit after A.
For the least positive WHOLE T-period P, consider the two cycle parities

    Qeven = XOR[t<P] r(t)*s(t),
    Qodd  = XOR[t<P] s(t)*r(t+1).

A one-time shift of the interleaved observation exchanges these parities.
The candidate uniform orientation is Qeven=0 and Qodd=1. If true it would
separate opposite phases whenever the compared whole periods match. It
would not by itself identify widths or prove equal observation periods
force equal whole periods; repeated oversized cycles can erase parity.

Only six named elementary controls will be tested: tails 0,1,00,01,10,11.
For each, compute the literal D(n)=n XOR((n>>1) OR(n>>2)) orbit of 100x;
check each step against the scalar bit formula, retain even/odd phases,
and identify its least whole D period by first return. Stop at a refutation;
no larger width, horizon, coefficient, or feature search is authorized by
this protocol. Finite controls are not a proof even if all pass.
