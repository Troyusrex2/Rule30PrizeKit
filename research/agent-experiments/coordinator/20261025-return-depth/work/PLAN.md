# Actual return-word cancellation operator

Previous turn: PROGRESS, complete actual Rule90 source bridge, 59 additional
replayed constants and upstream core PR23. Full P1 remains open. No blockers
or live prior jobs. Do not change the reference, checker, old archives or others.

For a right-edge row a define B_d(a)=a_d AND NOT a_(d-1), B_0=a_0,
Phi(a)=a XOR ((a<<1) OR (a<<2)), and Delta f=f o Phi + f over GF(2).
Define G_r(a)=Delta^r a_(2r-1) for r>=1, G_0=0, and
C_r(a)=Delta^r B_(2r)(a). The local source identity implies
C_r=G_(r+1)+G_r. Thus the complete source-channel sum telescopes.
For H a power of two and a=Phi^(H-1)(1), sum_(r<H) C_r(a)=c(2H-1).
This may be only another exact encoding, not an unbounded parity mechanism.

Test this telescoping identity and candidate simplifications before any
formalization: does the canonical G sequence become all ones beyond a bound
linear in the starting width, and is a fixed low-degree Boolean formula for
G plausible? Use independent direct submask sums; distinguish finite tail
observations from an infinite tail theorem. Compute symbolic ANFs of small
G_r exactly to falsify bounded-degree shortcuts. Do not refit a failed bound.

The first-return prediction from last turn remains separate: if rho is the
least changed bit of Phi^H1 vs1, positive channels below rho vanish; at even
rho the first such channel is odd. It is not a statement about the full sum.
Known H=16,rho=7 refutes rounding odd rho to the next even depth.

All mathematical jobs use the owned 300s/8GiB/2GiB-free guard. No two-machine,
computer-configuration, authentication or credential changes are authorized.
