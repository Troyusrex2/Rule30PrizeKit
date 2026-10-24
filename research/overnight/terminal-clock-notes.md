# The known response rewrites preserve the full triangular clock

Developed by Troy Lowry with OpenAI Codex, 2026-10-24. No prize or priority claim.

`Rule30TerminalClockResearch` proves an unbounded structural statement:
terminal `011 -> 01` and `101 -> 11`, behind any shared finite prefix,
preserve every equality between full Q-orbit states. If x and y are linked,
then Q^s(x)=Q^t(x) iff Q^s(y)=Q^t(y), for every s and t. In particular
Q^H(x)=x iff Q^H(y)=y for every H. Unlike the separate finite-clock
certificate, this result has no temporal-clock bound.

The indexed relation `Linked n x y` records a shared prefix of length n
and tails `[a,not a,1]` and `[a,1]`. `linked_diagonal` proves that one Q
step preserves the relation. The maps `inflate` and `deflate` reconstruct
each linked state from the other, as proved by `linked_inflate` and
`linked_deflate`. Applying them at any two times gives `iterate_equal_iff`.
`rewrite_equal_iff` extends this to any finite chain of the sound rewrites.

The complete module passes the unchanged working and pinned checkers:
50 replayed declarations and thirteen selected headlines in each environment.
See `terminal-clock-evidence/{catalog,pinned}/report.json`. The pinned
adaptation removes only module/import/export wrappers.

Independent Python controls cover every prefix through length eleven, plus
256 wide examples through prefix length 256: 8,446 cases and 1,122,302 checked
state pairs. The scalar Q trajectories have identical return times and
identical orbit equality relations. Sixteen independent built-in Rule 30
cones match 26,264 scalar cells. These finite controls are not the proof.

This identifies a useful remaining gap. The known response collisions do
not themselves discard full-state clock information. It is still unproved
that they generate every finite response collision; neither completeness nor
arbitrary finite-tail head-period detection follows from this module alone.
No statement about the vertical center column is proved.

The result is included in the updated PR 9 package, standalone proof and
evaluated computational essay. The seven catalog modules replay 399
constants separately; the combined source replays 394. The generated
auxiliary declaration sets differ, while all other named declarations agree
after namespace adaptation. No new essay has been sent to the prize API.

## Additional source audit

Four files from `ghywel/placego` at commit
`61fd612bb2c6f8fdd3a5667d5a8885d45f97195f` now pass independent full replay
against the pinned checker. They belong to their upstream authors; their
Lean files credit Local and the surrounding research record.

- `RootedReturn`: 24 declarations, four selected concrete headlines. A finite
  injective partial walk from a source terminates; its periodic-profile
  application proves that a rooted reset/integration walk returns to zero.
- `ParityMask`: twelve declarations, five selected headlines. Cyclic
  difference parity, complementary ambiguity, and odd-clock predecessor
  uniqueness under a parity condition.
- `JenPow2`: 151 declarations, nine selected headlines. Dyadic left-diagonal
  periods, run bounds, absence of a common eventual clock, and arbitrarily
  deep eventually white and eventually black diagonals.
- `BlackLock`: 28 declarations, two selected headlines. The nine-step black
  lock and its persistence. The kit already has a nine-black shield.

All 215 declarations replay with only standard axioms. The audit adds the
official statement import and replaces the broad Mathlib import by selected
Mathlib imports; every proof body remains unchanged. The initial umbrella
import hit its 300-second resource guard. An initial concrete-headline
selection also included a universe-polymorphic generic theorem, which the
checker does not accept as a headline even though full replay passed. The
final passes select concrete application theorems while replaying every
declaration, including the generic ones. A missing tactic import in the
narrow JenPow2 build was repaired by importing Linarith; no body was edited.

The exact upstream URLs, source hashes, pinned commit and complete checker
records are in `external-profile-audit/report.json`; reproduce with
`audit_external_profile_proofs.py`. No official reviewer status is inferred.
These are useful verified inputs, not a solution of the center-column
problem and not a claim of our authorship. The other two newly inspected
repositories had no Rule 30 Lean proof to adopt.

The clock-128 profile search was also repeated to 1.5 million pairs without
a counterexample. An earlier two-million-pair record was already stronger,
so it is preserved unchanged. Neither incomplete search proves completeness.

## Falsification target for the next unbounded step

`finite_or_rigidity_probe.py` tests two stronger finite-tail candidates:
the same nonconstant first-two-cell OR trace determines the head trace,
and a constantly black OR trace permits only a head of period dividing two.
At full clocks 128 and 256, searches of 1.5 million reachable profile pairs
stop at their state guards without a counterexample. Each checks 256
finite witnesses by independent whole-row scalar evolution. These are
incomplete searches and neither candidate is assumed in Lean.

The detector allows the one-cell fixed black state; requiring alternation
instead of period dividing two would incorrectly reject that trivial case.
It also recognizes the existing infinite-tail counterexample: profiles
87 and 168 have constantly black OR while the first needs period eight.
Its scalar causal-cone control checks 512 cells. Thus the finite-support
condition is essential in the candidate, not an omitted proof detail.

A separate informal Newton-coefficient check rejected monotonicity of the
highest temporal Newton index along finite spatial prefixes. In the
clock-32 profile graph, adjacent profiles 1502252310 and 1699433109 have
indices thirty and thirty-one. They have the same temporal period; this is
not a period-loss counterexample. No Newton-index invariant was proved or
adopted. A structural argument still needs to handle cancellation in OR.
