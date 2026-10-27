# Frozen finite-window test of the full cut31 boundary

The single short-gap packet suggests a sparse formula for the COMPLETE new
boundary pair, including its forcing. Test the formula on every legal
17-gate word from the3/5/no33 language, not on a longer sample trajectory.

Use the eight states (countdown d, gap g), g in{3,5},0<=d<g. Output1 iff
d=0; if d>0 decrement it, otherwise choose the next gap3 or5, with3 allowed
only after5, and set countdown to that gap minus1. Verify all states are
mutually reachable, so every enumerated finite path extends in both time
directions. Enumerate all distinct length17 output words from all states.

For each word build a(t): even bits are1-G(t/2), odd bits1, for0<=t<=32.
The exact triangular inverse Rule30 recurrence gives X31 andX32 at times0
and1. Set B=X32 and L=X31 AND NOT X32. Compare the isolated-packet formula
reported by prize_bridge_audit at08:34, including all K_i=G_i G_(i+3).

If the formula fails, classify its four-bit residual only by which of the
six local products K_j K_(j+8),0<=j<=5, are present. No sample fitting:
accept a correction only if each class is constant across ALL enumerated
legal words and the no-product class has zero residual. Record all input
words and actual/expected results. If this test fails, retain the failure;
do not increase window/depth or add features in this run.

This is an exhaustive finite local-function check. Its applicability to an
infinite gate requires the language-to-window and recurrence locality
arguments, not a trajectory extrapolation. No Lean proof, class closure
under a second reset, positive support gain, or prize conclusion is assumed.
