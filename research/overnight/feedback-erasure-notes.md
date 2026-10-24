# Finite feedback erasure and the next public proof audit

2026-10-24. Developed by Troy Lowry with OpenAI Codex. No prize or priority claim.

`Rule30FeedbackErasureResearch` proves that finite configurations with black
sets `{1}` and `{1,2}` have identical complete center and right-head traces,
although their initial right halves are not universally response equivalent.
One white-center step sends the initial right words `1` and `11` to `11` and
`101`; the earlier terminal rewrite makes those new states universally
equivalent. Feedback soundness then gives equality of every left column.
Both configurations are finite and nonzero, so the kit's existing finite
configuration theorem proves that the common center and right-head traces
are not eventually constant. Their left edges both equal 1. Neither
left-edge observability nor eventual center periodicity is decided.

The unchanged working and pinned checkers fully replay all 35 declarations
and 13 selected headlines. See `feedback-erasure-evidence`. The independent
standalone replay and fresh LeanLink notebook, now in public PR 9, include
all three response/profile/feedback modules: 238 declarations, 21 selected
standalone headlines, standard axioms, no message cells. Eight new actual
feedback controls pass through time 128 with built-in Rule 30.

The controls caught and corrected a coordinate error in the new test harness:
a Wolfram finite initial list starts at coordinate zero, so a nine-cell left
half ends at coordinate 8. Coordinate 9 is the first right cell; coordinate
10 is the second and differs already at time zero. The published original
terminal-rewrite control at coordinate 9 still tested a valid equality (the
first common right cell), but coordinate 8 is the direct center interface.
The new notebook uses 8 for the center and 9 for the right head. This changes
no proof. The previous journal description calling 9 the direct center
interface was incorrect.

## Independently checked public contribution

PR 10, by Luis Perez Morales and Claude (Fable 5.1), appeared at commit
`f6885abec122a9dcbb3160cb69312323bc075dc1`:
<https://github.com/WolframInstitute/Rule30PrizeKit/pull/10>.
It proves all-width period-three ether erosion and absence of every finite
ether wall. `audit_ether_erosion.py` copies that exact proof, removing only
module/export wrappers, and replays it with the unchanged pinned checker:
131 declarations, seven headlines, no new axioms, all pass. The report records
both source hashes. This is their result, not our contribution.

The local front certificate isolates one bad state among 24; all good states
remain good and have a decreasing potential. A right-edge speed bound limits
the initial run of bad states for finite perturbations of the ether. This
closes the ether-and-wall absorption route for period three. The separate
period-21 trap absorption, Q001, C3s001 and C3w(011) routes remain open. Do not
mistake ether erosion for exclusion of period three.

## Work still required

The full Problem 1 remains open. The fixed-driver counterexample rules out
repairing response reconstruction merely by requiring a nonconstant output.
A useful next test is whether the constrained period-three left dynamics,
whose boundary pattern is 010 and whose observed pattern is (*,0,1), admits
a nonlocal ranking that the weaker period-two constraint does not. This is
a candidate investigation only, not a supplied ranking or theorem.
