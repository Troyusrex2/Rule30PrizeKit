# Exact comparison with the verified periodic-OR theorem

The three-cell FULL-GATE return corollary is already implied by a published,
verified result. It must not be described as a new theorem from this lane.
The separately frozen earlier report explicitly disclaims novelty; this
note supplies the precise prior theorem and identifies the different
defect-observer hypothesis now being investigated/formalized.

## Prior exact source

Read in full: coordinator/20261026-periodic-or-clock-transfer/REPORT.md and
work/Rule30TwoPlateauClockResearch.lean, especially lines195 onward.

The exact headline is

    Rule30TwoPlateauClockResearch.actual_even_two_plateau_or_clock_rigidity

For Actual a, its parameter is the even shift2*n. Six successive columns
are n,m,l,k,h,g from older to newer. The only temporal input hypotheses are

    k(t+2*n)=k(t)+1;
    l(t+2*n)=l(t).

The conclusion is NOT(for all t, g(t+2*n) OR h(t+2*n)=g(t) OR h(t)).
There is no newest-output clock premise. The proof's paired six-cell
certificate leaves the two oldest profiles n,m free. The report records
full replay of5+138+54 constants in its three modules at official5473;
this note does not claim an additional replay.

In the head-first convention used here, (g,h,k,l,m,n)=(x0,x1,x2,x3,x4,x5).
Full gates imply x0 OR x1=1 at EVERY time, so they contradict the prior
theorem when x2 is anti-P, x3 is P-periodic, and P is even. Together with
the short j=0,1 cases, this already gives the full-gated three-cell result.

## The weaker observer relation is different

The new local assertion assumes only

    h0=E*h1,

where h_i=x_i(t+P)+x_i(t). Equivalently, the staggered observer
Y0=x0+E*x1 is P-periodic. It does not assume Y0=1 or periodicity of the
newest OR. The exact algebraic relation under this hypothesis is

    delta_P(x0 OR x1)=h1*(1+x0+E*x1)=h1*(1+Y0).        (C1)

At odd ticks this is h1*(1+x0), as noted by the root review. The right-hand
side need not vanish merely because Y0 is P-periodic. A genuine constant
initial leaf flip preserves h0,h1 and the observer-period premise, but
replaces the right side by h1*Y0. Therefore no silent substitution of the
prior OR-period premise is justified.

This comparison is about theorem hypotheses, not a claimed actual
counterexample under the new local theorem's birth hypotheses. The new
paper proof says those hypotheses together are impossible.

## Local ancestry scope

LOCAL-EXCLUSION-SCOPE.md uses genuine recurrences through x5, with x6,x7
as its two free oldest profiles. It therefore uses eight overlapping
columns, whereas the prior certificate already works with six. For an
actual finite-white word both are available, but one must not claim that
the new strip assertion relaxes every hypothesis of the old one.

The new mechanism is a pure propagation proof of the different staggered
observer exclusion. The old stronger-than-constant-OR theorem retains
its own credit, scope and verification. Neither result supplies arbitrary
distance clock preservation or physical Prize P1.
