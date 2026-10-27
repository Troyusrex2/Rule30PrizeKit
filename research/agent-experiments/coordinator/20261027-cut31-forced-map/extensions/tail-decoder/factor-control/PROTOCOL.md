# Fixed test of the proposed zero-preserving cut-31 spacetime decoder

Frozen before execution. This is one bounded falsification experiment, not a search or a Lean build. Evaluate both prescribed histories even if the first fails.

Inputs:

1. Pure carrier G(r)=[r mod 5=0], only r=0,...,31.
2. Actual G(r)=u empty(155+r), only r=0,...,31. Compute W0=1 and W(q+1)=step1(step0(Wq)) through q=186, where step_b(n)=((n<<1)|b) XOR (n|(n>>1)). Independently evolve the empty physical right half with the literal Rule30 truth table and alternating boundary through physical time373; compare every complete odd-time row with Wq, q=0,...,186. No later time or other seed is permitted.

For either G set a(2r)=1-G(r), a(2r+1)=1, giving exactly64 boundary bits. Set X0=0, X1=a. Construct only the triangular cone through depth34, solving each inverse stencil using the literal eight-entry physical Rule30 truth table. Independently verify each resulting stencil against `left XOR(center OR right)`. No temporal period is imposed on this finite cone.

For j=0,1,2,3 define B_j(t)=X(j+31,t), L_j(t)=X(j+30,t) AND NOT X(j+31,t), and M_j(r)=L_j(2r) AND L_j(2r+2). Define exactly:

    Y_j(2r) = B_j(2r+12) XOR M_j(r) XOR M_j(r+4)
                XOR M_j(r+6) XOR M_j(r+7) XOR M_j(r+11),
    Y_j(2r+1) = B_j(2r+13) XOR M_j(r+2) XOR M_j(r+3)
                XOR M_j(r+6) XOR M_j(r+7) XOR M_j(r+10)
                XOR M_j(r+12) XOR (M_j(r+3) AND M_j(r+11)).

Evaluate Y_j(t) only for t=0,1,2. All needed X times are at most26 and all needed boundary times at most59, within the fixed64-bit input.

Record:

- Y1(t)=a(t+14), for t=0,1,2, as the boundary-decoder control;
- all four positive-depth physical stencils k=1,2, t=0,1, both with the actual candidate Y0 and with its boundary replaced by zero;
- candidate Y0 values and the masked seam Y0(t) AND NOT Y1(t), t=0,1, to distinguish a failed wall from a failed interior update;
- exact constituent B/L/M observations for all evaluated Y values, the complete retained left cone, and the input gate words.

The claimed factor needs literal Rule30 compatibility, not merely a recovered boundary. Any actual-history stencil failure refutes this specified factor candidate on the actual trace. A pure-carrier failure alone is recorded separately. Passing these four stencils would establish only a bounded control, not universal commutation, class closure, support transport, CQ01Empty, or a prize result.

Run only this script in an owned remote worker process with a60-second/8-GiB/2-GiB-free guard. No Lean, Wolfram, new graph, other history, larger window, parameter sweep, or public write. Preserve failures without changing the candidate.
