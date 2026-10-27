# A hidden half-period birth cannot lie in the newest three coordinates

Complete paper proof, not yet Lean-certified. All additions below are XOR;
ordinary inequalities compare bits as0<=1. The evenness of P is explicit.

## Exact assertion

Let x_i(t) be one actual head-first trajectory satisfying

    x_i^+ = x_i + (x_(i+1) OR x_(i+2)).

Assume a whole return at2P, with P>0 even, and define h_i=x_i+tau_P(x_i).
If the oldest nonreturning coordinate j exists, then h_j=1 identically
and all older h_i vanish. Suppose additionally

    h_0=E*h_1,                                         (D0)

where E=1 at even ticks. Then j cannot be0,1 or2.

This is a statement about one actual orbit and its own half-shift. It does
not require the stronger r gate, any unconditional classification of twins,
or a selected newest-column period in place of the whole period.

The case j=0 is immediate: h0=1,h1=0. For j=1, the actual difference
recurrence gives Delta h0=1+x2. Equation(D0) gives h0=E and Delta h0=1,
so x2=0. The genuine recurrence of x2 then forces x3=0. Thus x1 is
constant, contradicting its unit half-shift defect. It remains to prove
the substantive case j=2.

## Reduction to a marked auxiliary profile

Set

    z=x2, f=x3, g=x4, k=x5, l=x6, m=x7,
    a=f OR g, y=h1, r=x1+z*y, O=1+E.

All of a,f,g,k,l,m,y,r are P-periodic, z is anti-P, and

    sum_(t<P) a(t)=1.                                  (D1)

The actual older recurrences include

    Delta f=g OR k;
    Delta g=k OR l;
    Delta k=l OR m.                                    (D2)

From the exact half-shift and marked recurrences,

    Delta y=1+f;
    Delta r=f+a*y^+;
    Delta h0=1+r.                                      (D3)

Using(D0) and E^+=O in the last equation gives

    r=E+y+O*f.

Taking its derivative and using the first equation(D3) gives

    Delta r=E*Delta f.

Consequently

    E*Delta f=f+a*y^+.                                 (D4)

Put q=y+O. Then q is P-periodic and

    Delta q=f,    y^+=q^++E.                           (D5)

The next deductions retain q as an auxiliary profile. It is never
identified with a genuine lower-clock Rule30 column.

## Two constraints on q

First,

    g*q=0.                                             (D6)

To see this, at a tick with g=1, equations(D2) give Delta f=1 and a=1.
Equation(D4) becomes E=f+q^++E, hence f=q^+. Together with f=q+q^+
this forces q=0.

Second, at every ODD tick,

    q=1 implies q^+=1.                                (D7)

Otherwise q=1,q^+=0 would give f=1 and y^+=0 at that odd tick, making
the left side of(D4) zero and the right side one.

Suppose q=1 at any odd tick t. By(D7), q(t+1)=1. Equation(D6) gives
g(t)=g(t+1)=0. The genuine recurrence Delta g=k OR l now forces
k(t)=l(t)=0. Hence Delta f(t)=g(t) OR k(t)=0. Since
f(t)=q(t)+q(t+1)=0, also f(t+1)=0, and(D5) yields q(t+2)=1.

Thus an odd one propagates to the next odd tick and the even tick between
them. Repetition and the positive even period P make q identically one.
Then(D5),(D6) force f=g=0 and therefore a=0, contrary to(D1). We conclude

    q(t)=0 at every odd tick.                          (D8)

## Genuine twins arise, and then disappear without a classification theorem

By(D5),(D8), at an even tick t,

    f(t)=q(t),    f(t+1)=q(t+2).

At an odd tick t, f(t)=f(t+1), so Delta f(t)=0. By(D2),

    g(t)=k(t)=0 at every odd tick.                     (D9)

At an odd tick, the other two genuine recurrences(D2) now give

    g(t+1)=l(t),    k(t+1)=l(t) OR m(t),

so g<=k at the next even tick. Positive even periodicity covers every
even tick, including the marked time0. Conversely, at an even tick the
next g is zero by(D9), so Delta g=g and(D2) says g=k OR l>=k.
Thus

    g=k at every time.                                (D10)

No general theorem about adjacent twins is invoked. Instead use the
additional constraint(D6). If q=1 at an even tick, then g=0 and(D10)
gives k=0 there. Thus Delta f=0 by(D2). The displayed formulas for f
at even and odd ticks force q=1 at the next even tick.

Again periodicity closes the propagation. Either every even value of q
is zero or every even value is one. Together with(D8),

    q=0 or q=E.

Equation(D5) makes f respectively the constant0 or constant1. In either
case Delta f=0, so(D2) forces g=k=0. Consequently a=f OR g is constant.
Its P-cycle sum is zero because P is even, contradicting(D1).

This completes the exclusion of j=2.

## Exact consequence and unbounded gap

Suppose an actual older prefix returns after P and at most three newer
coordinates are appended. If the resulting whole word returns after2P
and satisfies(D0), then it already returns after P. Otherwise its oldest
half-shift birth lies in those three coordinates and the assertion above
contradicts it. No minimal-period assumption is needed for this consequence.

For full all-time gates, (D0) holds for every even shift P. The elementary
triangular clock bound says that appending three bits to a P-returning
prefix gives whole return by8P: each successive bit has a periodic driver
and at most doubles the inherited whole return. Applying the previous
paragraph successively at shifts4P,2P,P therefore shows:

    all-time gates + older whole return P + at most three newer bits
      imply whole return P, for P positive even.       (D11)

This corollary is a paper derivation, not a claim of a fresh Lean replay or
of literature priority over existing short-extension results.

The proof does NOT establish a uniform bound on the distance of the oldest
birth from the observer. For j>=3, y is no longer driven by1+f and the
reduction(D3)-(D5) no longer applies. A valid unbounded proof must supply a
boundary transfer that preserves actual ancestry while moving toward an
older birth, or an appropriate induction invariant. Repeating this proof
at an older pair without such a transfer would assume gate inheritance.

No numerical search, new finite orbit certificate or Lean build was used
for this argument.
