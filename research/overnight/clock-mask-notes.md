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

## Subsequent rejected flux scores and a recognizer diagnostic

`finite_Q_OR_rank_probe` uses the fact that Q preserves finite width: on a
finite periodic orbit a score cannot strictly fall around a complete cycle.
It therefore searches without any positivity assumption. A positive result
could have excluded a head that stays unchanged while its adjacent OR stays
black. The one-step and two-step whole-word models, pattern lengths two
through four, returned numerical infeasibility. First spatial moments with
signed affine graph potentials also failed for these six cases. All twelve
feature-accounting controls passed, but no exact impossibility theorem or
finite-OR classification is inferred from the failed numerical searches.

`period_three_prefix_predictor` directly builds the constrained initial-prefix
tree through depth 42 and compares allowed future subtrees. For six future
cells, 4,096 valid prefixes of depth 36 have 1,004 distinct future trees.
Independent full-history controls pass 306 samples. These are finite data;
they prove neither regularity nor nonregularity of the infinite language.
They do not suggest a small fixed-state recognizer for the complete
period-three constraint. No claim about asymptotic minimum black density is
made from the finite prefix counts.

## Finite-preimage membership discovery

The next prototype inverts the three 010-boundary steps, with earlier heads
(*,0,1), using a 64-state transducer. Scanning from near the boundary toward
the finite zero tail gives an 89-state paired recognizer, minimized to 26
states. Controls compare 1,024 forward images, every current word below
2^14, and 512 wider random examples. They all pass. This is a discovery
prototype; the recognizer's all-width interpretation is not Lean verified.

An initial injectivity guess was false and was rejected by these controls.
Packed finite predecessors 55 and 56 both map to 400 in three steps; all
three rows have a uniform first triple. Thus a score using a finite
predecessor must retain the actual history or account for multiple choices.
One cannot silently treat the predecessor as a function of the current row.

The 26-state membership condition was added as an all-length necessary
restriction on the old row in the period-three graph. The length-two score
model has 60,936 vertices and hit its 30-second LP limit, without a result.
A separate finite-prehistory fit of that same score class became numerically
infeasible at initial width 20 (16,384 accepted pairs). No verified score or
impossibility certificate is asserted. The recognizer may support a more
appropriate history-dependent argument, which remains to be found.
