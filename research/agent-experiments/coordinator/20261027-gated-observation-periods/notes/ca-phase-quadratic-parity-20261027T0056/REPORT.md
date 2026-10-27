# Adjacent-pair cycle parities do not orient every canonical trace

This narrow proposed phase filter fails. It is not a Lean result and does not
refute nonlinear observability or the opposite-phase clock-birth descent.

For a finite canonical tail with two observations r,s and least whole T-period
P, define Qeven as the XOR of r(t)s(t), and Qodd as the XOR of s(t)r(t+1), over
0<=t<P. Shifting the full interleaved trace by one time step exchanges these
two sums, provided the same full period is used. A fixed unequal orientation
would therefore distinguish the two phases.

The recorded initial candidate had its orientation reversed. The first named
control, tail 0, gives r=s=01 and Qeven=1,Qodd=0. The literal A action fixes its
first bit. This is a convention error in the candidate, preserved in the
protocol and first output, rather than a new dynamical obstruction.

More decisively, the actual CA normal form fixes its third coordinate c. At
width three, r(t)=c is constant, so the summands defining Qeven and Qodd are
equal term by term. Both orientations therefore fail, even at the least whole
period. The additional named control x=000 verifies this exactly:

    D orbit: 32,56,38,61,34,59,36,63;
    least whole T period: 4;
    r=0000, s=0111;
    Qeven=Qodd=0.

Each integer update was independently checked against the scalar Boolean bit
formula. The first script stopped immediately at its first refutation; the
second tested only the analytically chosen three-bit control. No wider search,
new certificate, proof build or claim about optimal phase filters was made.
The pretest protocol, convention correction, scripts and exact outputs remain
alongside this report. No public write was performed for this isolated failure.
