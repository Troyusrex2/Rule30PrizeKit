# Exact black-event renormalization and its base-case obstruction

Status: paper derivation plus one prescribed inherited control. No new Lean
theorem, state/period/gap sweep, or finite certificate. The uniform gate-
halving theorem remains OPEN. The exact return relation below retains an
unbounded actual tail; it is not a finite closed reader.

## Domain and candidate

Use D(n)=n XOR((n>>1) OR(n>>2)) on finite natural integers, with low bits
at the observed head. Assume positive even P, D^(2P)n=n, and the selected
gates: head OR neighbor at even times, head at odd times. Both equal1.
The whole return extends these conditions to every time with the same
phase. P need not be least. This is the triangular dynamics, not the
physical-center sequence.

At a nontrivial even black-head event the previous paper's front lemma
gives a unique representation

    n=1+2^(4q)*m,   q>=1, m positive odd.

The trivial state n=1 is excluded from this representation. Define

    Phi(m)=(4*m) XOR((2*m) OR m).

Phi is defined here; it is not the differently oriented automaton A from
the positive-word work. The exact parameterized candidate was written in
PROTOCOL.md before any new control:

    D^t n = 1 XOR 2^(4q-2t)*Phi^t(m),  0<=t<=2q.       (3)

## Proof of the front relation and gap normalization

For k>=2, distributing the shift through XOR and OR gives

    D(2^k*m)=2^(k-2)*Phi(m).

Changing only the head bit commutes with D: D(v XOR1)=D(v) XOR1,
because both shifted parents are unchanged. Induction proves(3), using
only nonnegative exponents. At the last step the head and front overlap;
the formula correctly uses XOR rather than addition.

Phi preserves oddness. For odd m, Phi(m)=3 mod4, and Phi^t(m)=3 mod8
for t>=2. The latter follows from the first two leading ones followed by
1 XOR(1 OR anything)=0; no fourth front bit is fixed.

When q>1, equation(3) at t=2 gives the exact even-event update

    (q,m) -> (q-1,Phi^2(m)).                            (4)

There is no overlap with the head here, so the XOR is also an ordinary
sum. The next nearest black is exactly four positions closer. Thus every
nontrivial even black-head event reaches gap4 after q-1 macro steps,
where a macro step is R=D^2. The full gates are retained along an actual
gated orbit. This is a valid strict decrease of q UNTIL q=1.

For q=1, the two-step impact is1 XOR Phi^2(m), with low triple010. It is
not another black-head event. A separate return relation is necessary.

## Exact four-bit register over the actual tail

Write each even row as

    n_j=R^j n=16*m_j+r_j,   0<=r_j<16.

Spatial projection commutes with D, so m_j=R^j m_0 exactly. It is an
actual finite-white tail, not a freely chosen sequence of inputs.

Let r have low-first bits(h,g,f,e) and m have low bits(a,b,c,d). Expanding
OR as u+v+uv over F2 and cancelling in the two literal D updates yields

    h'=h+(e OR a)(1+g+f),
    g'=g+(a OR b)(1+f+e),
    f'=f+(b OR c)(1+e+a),
    e'=e+(c OR d)(1+a+b).                              (5)

All additions in(5) are XOR. Let sigma(r,m) be the integer represented
by these four new bits. The full exact macro update is

    (r,m) -> (sigma(r,m),R(m)).                         (6)

The even and following odd gates permit r in{1,9,2,6,10,14}. State9 has
h'=g'=0 under(5), so it cannot occur on an all-time gated orbit. Thus all
such orbits lie in the five register states{1,2,6,10,14}. This restriction
does not make the tail input finite or independent.

Starting with gap4 means r=1 and a=1. Formula(5) then gives

    sigma(1,m)=2+8*b*(c OR d).                         (7)

The fourth front bit is the displayed actual tail expression. In
particular the first impact can be state2 or10.

The previous branching condition is preserved exactly. At state2,

    h'=0, g'=1+(a OR b).

Survival of the next gate therefore requires a=b=0, in which case

    sigma(2,m)=2+4*c+8*(c OR d).

State10 has h'=0,g'=1 without a restriction on a,b,c,d. These are exactly
the alternatives e=1 OR(e=d_old=c_old=0) in the previous impact notation;
no black-support requirement has replaced the white branch.

The only admissible transition from a nonblack register state to a black
one is14->1. Indeed states2 and10 always have h'=0; from state6 the gate
requires a=0 and hence h'=0. From14, equation(5) gives

    h'=1,
    g'=1+(a OR b),
    f'=1+a*(b OR c),
    e'=1+(c OR d)(1+a+b).

All three latter bits vanish exactly when

    a=b=1 and c OR d=1.                               (8)

Thus immediately before a nontrivial first return, the actual row starts
with0,1,1,1,1,1 and its next two older bits have OR1. This is an exact
necessary and sufficient one-step return condition within the gated
register; it does not yet force additional older support.

## The partial first-return map, including normalization

Start with q=1: n=1+16m, m positive odd. Let J be the first positive macro
time with r_J=1, while retaining the actual tail update and every
intermediate gate. Under the supplied whole2P return, J exists and
J<=P. Equation(7) excludes J=1. Before this first return the register is
in{2,6,10,14}, and the last transition is exactly(8).

The returned tail is m_J=R^J m, not an independently selected word. It is
positive because D preserves the highest black position of a finite
positive integer. At this event the gap lemma gives

    v2(m_J)=4s,  m_J=16^s*u,  u positive odd.

The returned event has q=s+1. Apply(4) s times to normalize it back to
gap4. The resulting exact normalized return is

    N(m)=Phi^(2s)(R^J(m)/16^s),
    n_return=1+16*N(m),
    elapsed D time=2*(J+s).                            (9)

Here J is a guarded actual first-return time, and s is determined by the
actual returned tail. None of these is an arbitrary free parameter. The
first positive normalized return exists by the original whole return;
equivalently J+s<=P, since the intermediate normalizing events have q>1
and cannot equal the original q=1 row before normalization finishes.

This is a symbolic return relation for arbitrary tail width. It does not
prove that the guarded partial map has no finite orbit.

## Why the displayed map gives no support rank

For finite positive m, D and R preserve bit length L(m): their shifted
terms lie strictly below the highest black bit. Phi instead increases
bit length by exactly2, because its highest term4m cannot be cancelled
by2m ORm. Consequently normalization(9) satisfies

    L(N(m))=L(R^J m)-4s+4s=L(m).                       (10)

The pre-impact q decrease in(4) trades four gap cells for four active-tail
cells. Total support length is unchanged. Treating Phi's apparent support
growth as a contradiction would therefore be an error: its moving
coordinate origin exactly accounts for that growth.

Nor does a bounded segment of the register path prove a numerical
inequality N(m)<m. A path of fixed duration only reads a finite low
prefix by locality; farther older bits still evolve under the actual R.
They can determine numerical order without being observed by that
segment. A numerical rank would require a separate argument using the
full actual tail or the whole periodic premise. No such inequality is
claimed or tested here.

## Inherited infinite-tail return control

Use the already-known period-eight profile branch from
predecessor-periodicity-paper-20261026T2305/PAPER.md, with low-to-older
profiles234,21,154,149,86,89,101,149,... . At phase6 its head is black,
its next three cells are white, and its next cell is black: gap4.

At macro phases6,0,2,4,6 its register path is exactly

    1 -> 10 -> 10 -> 14 -> 1.

The corresponding actual tail low-four-bit values are7,14,13,11. They
satisfy(5), including(8) on the last transition. The full infinite tail
returns after eight D steps, so the normalized gap is again4. In binary
the phase-six tail repeats the low-first block1110 forever; its rational
two-adic value is-7/15, if that notation is desired. It is not a finite
natural m.

check_inherited_return.py checks only those four prescribed macro rows
and their register formulas. This orbit and its existence are inherited;
only its expression in the present return coordinates is being recorded.
It refutes a boundary-free strict reinjection decrease. It does not refute
the finite-white target.

## Assessment

The requested recursive relation DOES exist: arbitrary gaps reduce exactly
to gap4, and(9) is the partial normalized return there. The unresolved
part is a well-founded resource for this guarded actual-tail return. The
simple gap stops decreasing at4, support length is conserved, and the
infinite-tail control closes the same register path. The branch through
white older cells remains present throughout.

No further guessed rank, return table, gap sweep, or finite certificate is
justified by this derivation. A next proof would have to exploit finite
whiteness to exclude a recurrent guarded path of(6), while respecting
its actual R-driven tail. The independent isolated-marker/even-zero-run
suspension is another exact description of that waiting condition, not
an additional boundary-exclusion premise.
