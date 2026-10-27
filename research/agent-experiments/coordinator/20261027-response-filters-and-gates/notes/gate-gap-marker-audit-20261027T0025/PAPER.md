# The gap-four return as a white-pair-run suspension

Independent paper audit and exact correspondence. No Lean build, new scalar
control, state/period sweep, or numerical rank test. The finite-white
gate-halving target remains open.

## Domain and independent audit

Use D(n)=n XOR((n>>1) OR(n>>2)), with low bits at the observed head.
The supplied domain is a finite natural n, positive even P, whole return
D^(2P)n=n, and all selected gates: the head OR neighbor at every even time,
and the head at every odd time, are one. The return extends this same phase
to all time. Let R=D^2.

At a nontrivial even black-head event, the previously proved paper front
congruence gives n=1+2^(4g)m with g>=1 and m positive odd. Write

    Phi(m)=4m XOR(2m OR m).

For k>=2, D(2^k m)=2^(k-2)Phi(m), and D(v XOR1)=D(v) XOR1 for every v.
Consequently

    D^t n = 1 XOR 2^(4g-2t)Phi^t(m),  0<=t<=2g.          (1)

Every exponent in this induction is nonnegative. The XOR at the final
overlap cannot be replaced by ordinary addition. Phi preserves oddness;
for odd m its low two bits are11, and after at least two Phi steps its
low three bits are110. Thus for g>1 the exact two-tick event update is

    (g,m) -> (g-1,Phi^2 m).                               (2)

This is a genuine decreasing gap before impact. It is not a decreasing
support measure: the tail's bit length grows by four under Phi^2 while
the gap loses four bits.

I independently checked the complete current draft
gate-event-renormalization-20261027T0025/PAPER.md, SHA
c5db11e316954abe98f814262495ea0cd1141dfae4f32f12991c2bb1d8e8b358.
Its shared two-step identities, five-register restriction, guarded return,
actual tail projection and bit-length calculation are correct. In particular
the next four register bits, for old register(h,g,f,e) and actual tail
bits(a,b,c,d), are

    h'=h+(e OR a)(1+g+f),
    g'=g+(a OR b)(1+f+e),
    f'=f+(b OR c)(1+e+a),
    e'=e+(c OR d)(1+a+b).

The letters g in these copied register equations denote a bit, not the
integer gap parameter of (1). All sums in the equations are Boolean XOR.

On all-time gated orbits the register is in{1,2,6,10,14};9 is dead. A
nonblack register returns to1 only from14, exactly when a=b=1 and
c OR d=1. Thus immediately before a return, the actual row begins

    0,1,1,1,1,1, followed by a pair with OR one.           (3)

This uses the same actual tail at every step, rather than freely supplied
four-bit inputs.

## The marker and the remaining length of a white-pair run

Let E(t) be one at even times and zero at odd times. For an actual gated
trajectory X_t=D^t n define

    rho(t)=X_t(1)+E(t),
    w(t)=(1+X_t(2))(1+X_t(3)).

The sealed isolated-marker paper proves rho has no consecutive ones and

    rho(t+1)+rho(t)=w(t).                                 (4)

In the periodic two-sided extension, every finite maximal w=1 run has even
length. A run starting at time a and ending at a+2ell-1 has marker ones at

    a+1,a+3,...,a+2ell-1.                                 (5)

In particular runs starting at odd times produce even marker ones, whereas
runs starting at even times produce odd marker ones. At even times the
head is exactly rho, so only the first class produces black-head events.

There is an exact spatial interpretation of the REMAINING run length.
At an even black-head event n=1+2^(4g)m, (1) shows

    w(t)=1 for 0<=t<=2g-2;    w(2g-1)=0.                  (6)

Indeed before t=2g-1 the shifted front begins at position at least four,
leaving coordinates2,3 white. At t=2g-1 it begins at position two, and
Phi^(2g-1)m has its first two bits11. Thus the present white-pair run has
exactly2g-1 ticks remaining, counting the event itself. This conclusion
does not assume that this is the first marker in that run.

The updates g->g-1 in (2) are precisely consecutive even markers within
one odd-start white-pair run. No additional dynamical rank is hidden in
the gap decrease.

## Exact resolution of the gap-four waiting phase

Start at gap four: n=1+16m, m positive odd. The actual older tail beginning
at coordinate two is4m. Spatial projection commutes with D, so its white-
pair indicator is exactly

    w_m(t)=1-( bit0(D^t(4m)) OR bit1(D^t(4m)) ).           (7)

The initial event has rho(0)=1, w_m(0)=1 and w_m(1)=0. Hence its current
white-pair run ends at time zero. The next event must come from a later
run. Define

    tau = min{ a>0 : a is odd, w_m(a-1)=0, w_m(a)=1 }.     (8)

This minimum exists UNDER the supplied all-time gates and whole periodic
premise. The return at time2P supplies a future even marker, while w(1)=0
separates it from the initial run. Formula(5) identifies its run's odd
starting time.

If the run starting at tau has length2ell, then exactly:

* the first positive even black-head event is at T=tau+1;
* its gap parameter is g'=ell;
* successive normalization events occur at T,T+2,...,T+2ell-2;
* the first positive normalized gap-four event is at
  H=tau+2ell-1, the LAST marker and the end of that run.

The equality g'=ell follows by comparing the full run's remaining length
2ell-1 at its first marker with (6). Earlier even-start runs can occur;
they only produce odd marker ones and must not be dropped from the actual
gate conditions. The waiting time and their full actual ancestry remain
part of the return map.

There is no forced immediate return. At physical time two, (1) has low
triple010. Its next two-step head remains zero for every older tail.
Therefore T>=6, tau>=5, and the first macro return J=T/2 is at least three.
These inequalities are local lower bounds, not a bound on the full wait.

This is a natural desingularization of the g=1 branch: replace an undefined
gap during white-head phases by the actual white-pair-run clock (7), then
return at the next odd-start run. It does not remove or weaken any of the
intermediate gates.

## Match with the audited guarded return and its clock bound

In the four-register notation let J be the first positive macro return to
register1. Write the returned actual tail

    R^J m = 16^s u,    u positive odd.

The returned gap is s+1, so the marker interpretation gives ell=s+1,
T=2J and H=2(J+s). The audited normalized return is therefore

    N(m)=Phi^(2s)u=R^(J+s)m.                              (9)

The second equality follows from exact spatial projection and (1) applied
to16^s u. It emphasizes that the normalized tail is still a variable-time
iterate of the SAME actual shorter tail, not a new independently chosen
state or a free input word.

The bound J+s<=P is sound. First J<=P by whole return. If P<J+s, then
timeP in macro units lies on the forced normalization chain with gap
s+1-(P-J)>1. But the supplied whole return makes that row the original
gap-one row, a contradiction. Equivalently, the initial normalized marker
at time0 repeats at time2P, and the next odd-start white-pair run must end
no later than that event.

D preserves the highest black position of every finite positive integer.
Phi raises bit length by exactly two. Thus (9) preserves bit length:

    L(N(m))=L(m).

This return map is guarded by the entire actual register path. Its
identification with a return along the shorter tail does not by itself
transfer the gates to that tail. The local register formulas allow m to
begin11, as the inherited infinite-tail control below demonstrates; this
prefix violates the next odd head gate in that tail's own phase. No
finite-white theorem excluding that possibility under all future guards
has been proved here. Thus no induction on word width is supplied.

## Inherited control and remaining mechanism

No new control is run here. The inherited unanchored period-eight profile
branch has a gap-four event at phase6 and the register path

    1 -> 10 -> 10 -> 14 -> 1

at phases6,0,2,4,6. Its actual tail low-four values are7,14,13,11. The
phase-six tail repeats1110 forever and is not a finite natural integer.
The marker description gives the same normalized return after eight
ticks, with the new gap again four. This is the control already recorded
in the audited sibling draft, not a newly discovered trajectory.

Consequently the run correspondence alone gives no monotonicity of
successive half-lengths ell, and the local register alone supplies no
finite-white exclusion. Any positive proof must use finite ancestry to
rule out a recurrent guarded return, or transfer the gate/run conditions
to a strictly shorter actual word. Neither step is proved here.

The exact first-return constraint is nevertheless sharper than a guessed
numerical reinjection inequality: it specifies the retained phase, the
entire waiting condition, which white-pair runs count, the new gap, the
normalization time, and the continuing actual tail. No statement is made
about Prize P1 or a fixed physical-center observer.
