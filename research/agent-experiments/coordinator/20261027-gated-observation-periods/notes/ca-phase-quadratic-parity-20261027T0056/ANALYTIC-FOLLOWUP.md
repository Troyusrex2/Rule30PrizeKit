# The orientation error and a structural refutation

The first control immediately refuted the stated orientation: tail 0 has
Qeven=1,Qodd=0. This is because A fixes its first bit; the proposed orientation
had incorrectly assigned the complement to that channel. This convention
error does not decide whether the opposite orientation could work.

Before any further execution, there is a structural counterexample to BOTH
orientations. In the already derived literal three-bit CA normal form, the
third coordinate c is fixed by T. Thus r(t)=c is constant at width three.
Consequently r(t+1)=r(t), and Qodd=Qeven term by term for every return period.
In particular c=0 gives both sums zero. This is unrelated to oversized clocks.

One additional named check is authorized to confirm the conventions: x=000,
the literal finite word 100000. Compute its first whole return and compare
the scalar and integer updates. No other control or search is needed. The
phase-sensitive quadratic adjacent-pair cycle sum cannot distinguish all
canonical opposite phases. This does not refute nonlinear observation or a
different phase criterion.
