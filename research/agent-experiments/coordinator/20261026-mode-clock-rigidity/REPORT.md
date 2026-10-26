# A uniform clock theorem for the lower mode readout

For arbitrary Boolean traces q,k,l,m,n and any clock R, assume

```text
q(t+1) = q(t) XOR NOT k(t)
k(t+1) = k(t) XOR (l(t) OR m(t))
l(t+1) = l(t) XOR (m(t) OR n(t))
k(t+R) = NOT k(t).
```

Then **`S(t) = q(t) OR (NOT k(t) AND NOT l(t))` is not R-periodic**.
There is no period premise on q or l and no finite-support premise.
The headline is `Rule30ModeClockRigidityResearch.mode_readout_no_half_clock`.
This is a clock theorem, not an inverse for q.

For an actual triangular Rule 30 history, if h flips after 2R steps and
its immediate older profile k flips after R steps, then
`lowerReadout(g,h,2R)` cannot repeat after R steps. The actual-history
headline is `actual_lower_readout_no_half_clock`. It assumes neither a
period of g nor a period of the profile immediately older than k.
All indices and recurrences are explicit in the source.

## Argument

Suppose S repeats after R steps and put `v(t)=q(t+R) XOR q(t)`.
The complemented driver and k's antiperiod imply that v flips every step.
At any time where v=1, equality of the two readouts forces `q=k`;
if k=0 it also forces l=0. Unlike the initial draft of the argument,
this implication does not require l to repeat after R steps.

Using the same condition two steps later, q's update forces
`k(t+2)=k(t+1)`. If k(t)=0, the k and l recurrences also force
`k(t+1)=0`. Applying these implications on alternate time steps shows
that after time one, a zero of k can never be followed by a one.
But an antiperiodic k has a future zero and, R steps later, a one.
This contradiction proves the theorem for all clocks simultaneously.

The final module SHA-256 is
`f4f31ad9d570647566cf5036ce7ab34db7197e873a99706cdb4734da4df2cc65`.
All **10 constants** and two headlines pass the full unchanged official
checker at kit pin `5473ffd075f63c9d626e63b8455805d4831b39ca`,
Lean 4.35.0, with no new axioms. Final guarded build/replay: 1.631 s,
peak owned RSS 779,497,472 bytes on G913. Checker SHA-256:
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
This is local full replay; no Wolfram backend or human verdict is claimed.
The first draft hit a simplifier recursion limit; explicit small Boolean
lemmas fixed it without changing resource limits or the checker.

## Independent controls

The two decisive Boolean implications are exhaustively checked in Python.
An independent cyclic enumeration checks 196 local histories at R=1,2,4
without assuming a period of l. Counterexamples after separately removing
k's antiperiod, k's recurrence, or l's recurrence demonstrate that those
premises matter. These controls use the literal Rule 30 truth table.

## Why clock preservation does not solve the observer

An ancestry-free local inverse is false even when q is computed from
literal g/h plateau histories, rather than supplied as an unrelated trace.
At R=8, P=16, two six-cell strips with period 32 have the same full S
trace but different q traces. Rotating both by two steps gives different
q(0) with identical observations. The independent audit checks every
Rule 30 update at the four newest cells, h's P-antiperiod, k's R-antiperiod,
l's R-period, the definitions of q and S, and the target-bit difference.
The complete rotated rows are in `genuine-local-collision-audit.json`.

**The two oldest strip inputs are arbitrary. No finite white ancestry
has been established.** This refutes the inverse on that relaxed local
class, not the actual-history observer with its boundary assumptions.
The candidate mode observer on actual finite prefixes remains open.
The earlier relaxed collision with a freely chosen q is also retained;
its missing h/g consistency is stated explicitly in its metadata.

Adjacent-equality strip searches similarly find nonalternating cyclic
walks at every tested width 4..14 when the two oldest cells are arbitrary.
Those walks were checked cell by cell, but are not white-ancestry
certificates. This method cannot supply a local rigidity proof at those
depths. The prefix graphs through clock 64 show only period-two nonzero
equal adjacent traces and no adjacent period drops, but require all
prefix ancestors to have the tested clock. These are finite observations,
not uniform no-drop or equality theorems.

## What remains

Together with [even-clock plateau rigidity](../20261026-even-clock-rigidity/REPORT.md),
this gives two uniform obstructions to losing clock information. It does
not construct the mode inverse, classify longer plateau chains, prove
the full penultimate-bit observer or invariant sink separation, or bridge
a fixed sheared depth to the physical center column. P1 remains unsolved.
No new prize essay, submission, or PR accompanies this research archive.
The previous 3,031 selected hashes across 36 archives remain unchanged.
