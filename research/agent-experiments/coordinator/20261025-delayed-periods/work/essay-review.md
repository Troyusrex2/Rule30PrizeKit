# One delayed defect forces unbounded spatial periods in Rule 30 reconstruction

Troy Lowry, with OpenAI Codex

Draft for human review. Partial result for Problem 1 research; not a solution
to any prize problem. Not submitted to the Wolfram API.

The exact claim is about the kit's sideways reconstruction, not the canonical
single-seed center column. Begin with a period-four temporal column whose even
entries are black and whose odd entries alternate white and black. Change
just the white entry at time 8j+5 to black. The corresponding constrained start
Theta(free j) is eventually periodic in space. Every eventual spatial period
P>0 nevertheless satisfies j<2^P, whatever spatial transient is allowed.
Choosing j=2^M therefore gives an explicit input for which every eventual
spatial period exceeds M. The headline is
Rule30Submission.theta_explicit_large_periods.

Rule 30 updates a cell to left XOR (center OR right). The single-seed pattern
and its center column motivate Prize Problem 1: does that column ever become
periodic? This essay does not answer it. It examines the complexity of an
auxiliary reconstruction that appears in the open period-two reductions.

Finite computations first gave spatial periods 7, 14 and 28. A period 56 example
showed that these were not an exhaustive catalogue. A symbolic lifting rule
allows a spatial period to double when moving to an earlier temporal row.
The present argument explains why a bounded catalogue cannot suffice at all,
even in a one-defect family satisfying four necessary finite word constraints.

Write pure(t)=[t mod 4 is not 1]. Its odd-time free input is 0, 1, 0, 1, ... . In
the delayed family only free index 4j+2 is changed from 0 to 1, producing one
111 run. Uniform Lean proofs show that the free input contains none of
00, 11111, 010110 or 1011010. The construction is therefore more constrained than
an arbitrary temporal word, while finite-right realizability remains open.

The proof has four steps. First, a 312-cell reconstruction table proves that
the base defect's recurrent spatial tail differs from the pure periodic
background. Second, outer locality preserves agreement beyond a finite
spatial depth for every fixed elapsed time. Shifting two differently delayed
inputs then shows that their reconstructed rows cannot agree on a spatial
tail. Third, a row of eventual spatial period P has only 2^P possible residue
words, and any period of a later defect is inherited by all earlier defects.
If j>=2^P, pigeonhole would force two distinct delays to have the same tail.
Thus j<2^P. Finally, a finite temporal-profile argument proves that every
member really is eventually periodic in space; unboundedness is across the
family, not nonperiodicity of an individual spatial row.

The notebook embeds its complete Lean source as an icon in the proof cell.
It obtains the kit path from RULE30PRIZE_KIT, uses LeanImportString to create
rule30Submission, displays the headline types and axioms, and invokes the
LeanLink full kernel check. It needs no local research files on a verifier.

Validation before the notebook: a cold core build and full replay of all 173
declarations passed at kit 3eca23c0a9fa6b153313655e6d51835406c2d06e. After the
verifier moved, the identical catalog source passed full replay at
0090056412733accaa27643d3cbbf982104f2251 with no new axioms. The standalone
Rule30Submission source and the notebook receive separate checks recorded
with this draft. Lean 4.35.0 and the unchanged official checker are used.

The unresolved questions are substantial. No member is proved to arise from
an actual finite right half. No lower bound on spatial black density, no
critical-charge inequality, no absorption result and no canonical center
nonperiodicity theorem follow. These statements cannot be promoted to a
prize solution by observing more finite cases.

References: the official Rule30ZeroBoundary definitions, reconstruction,
outer locality and Jen pigeonhole lemmas at the stated kit pin; the Rule30
Prize Problem1 statement; and the full source in upstream PR25:
https://github.com/WolframInstitute/Rule30PrizeKit/pull/25 . The separate
period-lifting result is PR24. Both are proposed partial catalog contributions.
