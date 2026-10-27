# Whole-orbit extremality: exact suffix transfer, missing gate transfer

Status: elementary paper lemmas plus one named inherited plateau control.
No Lean build, state/width/period sweep, finite certificate, or public
write. Uniform gate halving remains OPEN. This assessment does not rule
out every use of global extremality.

## Actual finite orbit and prior work

Let D(n)=n XOR((n>>1) OR(n>>2)), R=D^2, with low bits at the head.
Assume P>0 is even, R^P(n)=n, and the selected head-OR gate at even D
times and head gate at odd D times are1. The whole return extends these
conditions to every time with their original phase. All integers here
are finite, so ordinary numerical extrema exist.

The prior orbit-quotient-20261026T0720 report tried18 context-dependent
lexicographic rank templates and obtained UNSAT results, not a general
rank impossibility theorem. block-clock-20261026T0625 likewise records
failed finite-memory templates and timeouts. The present choice is a
maximum or minimum over the entire actual orbit; it is not one of those
fitted local ranks, nor a comparison based on a bounded observation
window. The ca-canonical-observer-20261026T2314 report keeps aligned
observation and phase separation distinct. No theorem from that report
identifies their missing hypotheses with numerical extremality. This
paper does not assume that canonical normalization preserves numeric
ordering or that extremality proves either observer condition.

## Exact global suffix-extremality lemma

Let O={R^t(n):0<=t<P}, and choose M=max O. Since R permutes this finite
orbit, O is also the full R orbit of M. For every k>=0 define
pi_k(x)=x>>k. Directly from right shifts and the Boolean operations,

    pi_k(Dx)=D(pi_k x), hence pi_k(R^t x)=R^t(pi_k x).

Since pi_k is monotone for ordinary finite integers, for every t,

    R^t(pi_k M)=pi_k(R^t M)<=pi_k M.

Thus EVERY suffix pi_k M is the maximum of its entire shorter ACTUAL
R orbit, and R^P(pi_k M)=pi_k M. The same proof with inequalities
reversed shows that suffixes of the full-orbit minimum are full-orbit
minima. No gate premise is needed for this lemma; finite whole return
is used to make the complete orbit finite and phase-independent.

This is a valid transfer to shorter actual dynamics. Unlike the earlier
bounded-return comparison, it uses every bit and every time. It does
not transfer the gate hypotheses.

## Exact highest-change and clock-birth constraints

For any s, if R^s(M) differs from M and j is their largest differing
bit index, then

    bit_j(M)=1,  bit_j(R^s M)=0.                       (1)

Otherwise all more significant bits would agree and R^s M would exceed
M. At a minimum the direction is reversed. Equivalently, if the whole
older suffix above j returns after s but bit j flips, then that bit is1
at a maximum and0 at a minimum. This applies in particular to a genuine
clock-birth bit over a returned older suffix. It requires an actual flip;
an oversized return may make the flip zero and supplies no constraint.

The one-step macro specialization is explicit. Write x_i=bit_i(M). The
literal two-step identity is

    bit_j(RM)=x_j + gamma_j,
    gamma_j=(x_(j+3) OR x_(j+4))*(1+x_(j+1)+x_(j+2)),  (2)

with F2 addition and multiplication. It follows by substituting two D
updates and expanding OR=u+v+uv. If j is the greatest index with
gamma_j=1, then all older gamma_i vanish and x_j=1 at a maximum (0 at a
minimum). The support is finite, so the greatest changed index exists
whenever RM!=M.

These constraints are rigorous for unbounded widths, but apply to every
finite triangular orbit, whether gated or not. Bits on clock plateaus
need not flip when their older suffix returns, so(1) leaves them free.

## The precise gate-transfer issue

At every even row the gates are equivalent to h=1+g and f<=g, where
h,g,f are the first three bits. Over an all-time gated orbit the four-bit
register belongs to G={1,2,6,10,14}; register9 is dead at the next macro
step. This is the exact five-register reduction from the previous paper.

Suffix extremality does not preserve these inequalities. For the simple
genuine gated state6, R(6)=6 and the selected gates hold forever, so6 is
both its global maximum and minimum. Its immediate suffix3 is likewise
R-fixed and extremal, but its phase-zero gates fail: D(3)=2 has odd head0.
The previously proved one-step temporal shift repairs this example, since
the head of6 alternates. The example therefore rejects unshifted gate
projection, not all possible phase-adjusted induction. For the open
variable-head case, no fixed phase shift has been established.

Choosing a global maximum gives gates at that phase plus the extremal
constraints(1) for the whole orbit. To induct on a shorter tail one
still needs gates, or another sufficiently strong closed condition, at
EVERY phase of the shorter orbit. A maximum of the shorter orbit supplies
no such missing phase information by itself.

The conditional-flip case is compatible with the already-known local
gated-return argument. If a whole older tail returns and the appended
penultimate bit flips, the two copies of every older phase constrain its
reset latch in opposite states. This is exactly the setting of the local
return exclusion, rather than a new induction through an arbitrarily
long plateau. When that flip is zero, no second state over the same
older phase is available; this is where the current extremal argument
stops. No unsupported constant-column propagation is inferred from only
even-time white values.

## A complete finite-white orbit refutes the local-maximum shortcut

Before computation PROTOCOL.md stated the stronger candidate:

    Every nontrivial finite R orbit has its maximum outside G.       (3)

Only the already-known genuine plateau binary1101100100 and its two
one-cell children were used, namely868,1736,1737 in the present integer
convention. Their32 literal D steps were checked against an independent
per-bit scalar update, and their exact minimal D period32 was confirmed.
This is the existing plateau family from
even-clock-lifting-20261026T2120/REPORT.md, not a new search.

For child1736, the complete two even-time phase orbits have maxima

    M0=1782, M0 mod16=6;
    M1=1342, M1 mod16=14.

Both lie in G, so(3) is FALSE on genuine finite-white data. These are
full-orbit maxima, not maxima of a truncated segment. Starting at1782,
the first selected gate failure occurs at D time3; starting at1342 it
occurs at time4. Therefore neither is an all-time gated counterexample
to the real target. For example,1782>>1=891 is the maximum of the
corresponding actual parent orbit and has register11, illustrating the
distinction between preserved extremality and local gate membership.

CONTROL.json retains all six fixed phase-orbits, their maxima and gate
failure positions. No other widths, periods, inputs, minima, or rank
templates were searched. The companion head flip explains why this is
a useful plateau control: the child clock does not double, so a chosen
head value can change the low gate pattern at the same extremal parent
phase without creating a different older trajectory.

## What this establishes and what remains

The global approach genuinely avoids the unseen-tail objection to a
bounded numerical comparison. It yields exact extrema on every shorter
actual suffix and fixes every clock-birth bit at the extremal phase.
It does not, in the argument developed here, turn the gate language into
an inductive condition on those suffixes. The strongest simple local
shortcut(3) is explicitly false.

A further proof would need a relation among ALL extremal fibers or a
canonical phase selection that carries a phase-valid temporal condition
to the shorter tail. Merely replacing a global maximum by a minimum, or
reusing a bounded local rank, is not such a relation. This lane stops at
that exact missing transfer, without another speculative template or
larger census. The all-time finite-white gate-halving obligation remains
unchanged.
