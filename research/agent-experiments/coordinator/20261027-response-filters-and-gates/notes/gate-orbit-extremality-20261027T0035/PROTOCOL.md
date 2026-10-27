# Whole-orbit extremality candidate, before tests

Actual finite D(n)=n XOR((n>>1) OR(n>>2)); R=D^2. Assume positive even P,
whole R^P(n)=n, and all selected even-OR/odd-head gates. The gates retain
their phase under R. Choose M to be the largest ordinary integer in the
ENTIRE finite R orbit, or choose its minimum. This uses every tail bit and
all orbit phases, not a bounded observation window.

Exact candidate constraint: at every spatial suffix k, floor(M/2^k) is
the maximum of the full R orbit of that shorter ACTUAL tail. Moreover, if
j is the greatest bit where R(M) differs from M, then at a maximum M_j=1
and
  (M_(j+3) OR M_(j+4))*(1+M_(j+1)+M_(j+2))=1,
while the same toggle vanishes at every older index. At a minimum the
changed bit is0. The same extremal comparison holds for every R^s.

Try to combine this exact suffix-extremality transfer with the gates to
obtain a shorter gated problem or a forbidden boundary pattern. Do not
assume suffixes inherit the gates, monotonic numeric return, or an
unproved observability criterion. No state/width/period sweep, new finite
certificate, or build is proposed.

Prior work to inspect: orbit-quotient-20261026T0720 (failed finite-template
lexicographic ranks and canonical orbit representatives),
block-clock-20261026T0625 (context-dependent rank templates), and
ca-canonical-observer-20261026T2314 (separate aligned/phase-separation
obligations). A whole-orbit maximum is not one of those fitted local ranks.

Named falsification before execution: use ONLY the already-recorded
finite-white plateau binary1101100100 and its two one-cell children,
integers868,1736,1737 in the present low-head convention. Retain all32
literal D rows, check the known whole/minimal32 clock, and inspect the
maxima of their two R phases. Candidate shortcut to falsify: every
nontrivial R-orbit maximum lies outside the gated register set
G={1,2,6,10,14}. An extremum in G would not itself be an all-time gated
counterexample; record a failing selected gate elsewhere in that orbit.
This is one inherited plateau family, not a state/period/width sweep.
