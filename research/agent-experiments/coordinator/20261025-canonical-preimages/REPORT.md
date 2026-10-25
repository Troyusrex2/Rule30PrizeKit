# Finite look-ahead does not ensure canonical backward lifting

Problem 1, Q01, CQ01 and EdgeObservable remain open. This checkpoint proves
a uniform obstruction to one attempted shortcut in the divided-difference
observer strategy. It does not refute the observer target.

## The checked statement

For **every natural horizon H**, there are actual canonical ages U>V=1 and
a nonzero initially finite field h such that:

- A(t,p)=cell(U+t,p) and B(t,p)=cell(1+t,p) are the actual single-seed rows.
- h(0) is supported inside A(0) XOR B(0).
- Through time H, h obeys the divided-difference update D and the common-gauge
  constraint W from the previous agent brief.
- h(t,0)=0 for every t<=H.
- h(0) has **no left-finite predecessor** satisfying both the previous-time
  subset and W constraints and mapping to h(0) under the previous D step.

The explicit choices are e=2H+4, U=2^e, V=1, and h the ordinary physical
evolution of an isolated pulse at position U. Its use as a common auxiliary
field is asserted only through H. This pulse **does not carry the canonical
left edge** at -U. No all-time invisible canonical mode has been found.

The exact theorem is
`Rule30CanonicalPulseResearch.arbitrarily_long_nonliftable_canonical_modes`.
Both sources have passed the unchanged official checker at verifier commit
0090056412733accaa27643d3cbbf982104f2251, including complete kernel replay
and no new axioms. The reports record 49 and 45 replayed declarations,
including generated proof declarations; these are not 94 independent new
mathematical results. The first source is core Lean. The canonical corollary
imports the kit's Mathlib-based TFunction module.

## Why the obstruction works

The kit already proves that, at time 2^e, the rightmost e+1 cells return to
their initial single-pulse pattern. Locality separates that pulse from the
rest of the older row and from the younger seed row for the requested H.
On that separated cone the physical pulse satisfies D and W.

A predecessor satisfying subset and W would make seed XOR predecessor a
physical Rule30 predecessor of the row with black positions {-1,0,1,U}.
The helper `pulseTarget_no_leftFinite_preimage` proves uniformly for U>=2
that this row has no predecessor white sufficiently far to the left.
The proof propagates its white left tail to position 0, then the three
black cells force predecessor cells 1 and 2 white. The white gap forces
whiteness up to U. The pulse at U forces predecessor cell U+1 black,
contradicting the white output at U+1.

This last argument formalizes an elementary preimage obstruction. No claim
of literature novelty for that local fact or the kit's dyadic return theorem
is made. The contribution here is their precise uniform combination with
actual canonical ages and the proposed D/W lifting rule.

## Experiments and independent controls

`backward_fields.py` computes exact F2 spaces at 190 pairs 2<=U<=20,
1<=V<U. At the sampled horizon 4U each current space is one-dimensional,
spanned by the actual difference. This is finite evidence only. The followup
scans each horizon through U: the largest first full-finite-image inclusion
is 5, while the largest first restricted-image inclusion is 8. These numbers
are not uniform bounds. The Lean theorem explains why a fixed look-ahead
independent of the ages cannot make that lifting implication valid.

The dyadic pulse experiment covers e=2..12. Independent controls compare
17,157 canonical scalar cells with packed evolution, replay 325 mode
timesteps, check all 256 assignments in the local recombination identity,
and exhaust 32,512 small finite preimages. Seven known seed-preimage controls
also pass. None of these computations is a Lean proof premise.

The original pulse-bound script failed at U=4: the younger seed cone arrived
sooner than its proposed bound allowed. The original script and failed guard
log are retained. The corrected bound is
min(floor((rho-2)/2), floor((U-3)/2)); all eleven probes pass. The final Lean
theorem uses its own exact inequalities, not the experimental bound.

## What this changes next

A fixed finite check of initial subset, D, W and zero center cannot justify
backward closure. An infinite-horizon lifting theorem remains possible.
Another possible route must exploit the mode's canonical left edge, which
the pulse obstruction lacks, or stronger ancestry constraints. The sufficient
observer target in the prior brief remains open.

No new catalog PR or prize API submission is made for this checkpoint.
The prior all-width product-parity result remains in PR27. Its large notebook
still lacks a complete fresh-process replay; the earlier passed small canary
and unevaluated preview do not establish that. No new memory waiter is running.

## Reproduction

First run `python -B verify_artifacts.py` to check archived bytes and scope.
Copy work to scratch before executing it. Adapt the local verifier and lake
paths in `replay.py`, retaining the exact pin and unchanged Check.lean.
Run `guard.py replay.py Rule30PreimageResearch`, then
`guard.py replay.py Rule30CanonicalPulseResearch`. The second module imports
the first owned build. Python 3.12 and psutil are used by the guard.

Run the computational scripts under the same guard, in this order:
`backward_fields.py`, `scan_lift_delays.py`, `dyadic_pulse_checked.py`,
`independent_pulse_controls.py`. The intentionally failed original probe is
retained for audit and is not part of the passing reproduction sequence.
The standard limits remain 300 seconds, 8 GiB owned-tree RSS and 2 GiB minimum
available system RAM. No settings, license or computer configuration is changed.
