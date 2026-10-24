# Local clock masking: a verified obstruction, with an open extension

Developed by Troy Lowry with OpenAI Codex, 2026-10-24. No prize or priority claim.

Let five temporal columns satisfy

    a(t+1) = a(t) XOR (b(t) OR c(t))
    b(t+1) = b(t) XOR (c(t) OR d(t))
    c(t+1) = c(t) XOR (d(t) OR e(t)).

Put H = 2n. Assume a has period 2H, b reverses color after H, and c and d
have period H. Then a OR b is not constant black and does not have period H.
An additional predecessor z with derivative a OR b cannot have period H
either. `Rule30ClockMaskResearch` proves these statements with every premise
explicit, including an application to the actual triangular Q orbit.

All 13 generated declarations and five selected headlines passed full kernel
replay using both the working and unchanged pinned checkers. The source
hashes and exact checker outputs are in `clock-mask-evidence`. The Wolfram
control checks 192 qualifying cases among 512 finite starts and compares ten
whole-row Q evolutions with built-in Rule 30 along the corresponding slanted
causal cones. Every finite control passes. These calculations do not replace
the unbounded Lean proof.

The proof introduces K(t) = a(t) XOR a(t+H). Constant OR would force
K=0 to imply c=d=0. The update of K then implies d is pointwise at most c.
Consequently K XOR b alternates each step. Its half-clock would have to be
both even-periodic and color-reversing, a contradiction.

This only protects the neighborhood of a clock onset. It does not propagate
the clock through an arbitrarily long prefix, prove finite-tail head-period
nonloss, or address the vertical center readout. In particular, even proving
all fixed diagonal periods unbounded would still leave the center problem.

## Separate unverified discovery and rejected candidates

The period-three left constraint with boundary 010 and head pattern (*,0,1)
is equivalent over one cycle to a uniform first triple. The numerical probes
tested signed local counts with a head-dependent period-three ether prefix
automaton. Fits through width 16 failed exact rational checks on wider
explicit finite words. `period-three-rejected-small-fits.json` records those
counterexamples to the particular fitted coefficients.

The whole-word transducer computes three exact scalar steps while scanning
arbitrary finite words followed by zeros. It was checked against 128 actual
updates and whole-word feature differences. Its LPs found no rank at pattern
length two or three, even when both first reference defects were restricted
to positions divisible by three. These are numerical failures of these
models, not kernel-verified impossibility theorems or results about C3w.
One unrestricted length-three run hit its 30-second limit; the restricted
run returned numerical infeasibility after about 27 seconds.

The fixed-clock profile probes for clocks 1,2,4,8,16,32 completed, consistent
with the earlier completed clock-64 probe. The clock-128 probe remains
incomplete. `clock_onset_extension_probe` starts from all 132 period-eight
profile pairs with infinite right continuations and exhausts 1,908 reachable
period-sixteen pairs without finding a later head-period drop. None of these
graph statements is Lean verified, and infinite right tails are allowed in
the extension experiment. They do not prove the arbitrary-clock extension.

## Literature check

[Michael Brunnbauer's 2019 note](https://brunni.de/findings30/) discusses
nondecreasing right-diagonal periods for the single-seed orbit using trailing
zeros. That is a relevant antecedent, not a verified premise here. Its
trailing-zero argument has not been formalized or audited in this work.
The stronger conjecture about every finite Q start must be kept separate
from statements restricted to the single seed. The local theorem above was
derived independently before this literature check; no novelty is asserted.
