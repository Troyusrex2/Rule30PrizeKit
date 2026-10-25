# One delayed defect forces unbounded spatial tail periods

**Problem 1, Q01 and CQ01 remain open.** This is a uniform theorem about
synthetic constrained starts, not a nonperiodicity theorem for the canonical
single-seed center column. Every member below is spatially periodic; the
required periods across the family are unbounded.

## The proved family and quantitative bound

Let `pure(t) = [t mod 4 != 1]`. At the even times this temporal column is
black; its odd-time free bits alternate 0,1. Define `input j` by changing
only the white entry at time `8*j+5` to black. Its free input differs from
alternation only at index `4*j+2`, producing one run 111. Lean proves that
this free sequence avoids 00, 11111, 010110 and 1011010, for every j.

For the official `Theta (free j)`, the module proves all of the following:

- It is a valid constrained start (`InX`).
- It is eventually periodic in space.
- Every eventual spatial period P>0 satisfies **j < 2^P**, regardless of
  the spatial transient.
- The explicit input j=2^M has no eventual spatial period P<=M.

The [catalog module](work/Rule30DelayedDefectPeriods.lean) is proposed in
[PR25](https://github.com/WolframInstitute/Rule30PrizeKit/pull/25), head
`16528d6d9e0a09c54edeea5e73044beb9e63e495`. Exactly three files differ from
current upstream main: the 573-line module, its public import and catalog row.
Saved head/body/files/remote/raw-source readbacks agree. The PR is open,
with no review decision or GitHub checks in the saved readback.

## Why the argument is unbounded

A 312-cell table establishes the recurrent spatial tail of the base defect
and separates it from the pure background. The official outer-locality
theorem preserves agreement beyond a finite depth for every fixed elapsed
time. Temporal shifts therefore make any two differently delayed starts
distinct modulo finite spatial prefixes.

A P-periodic spatial tail has at most 2^P residue words. Any spatial period
of delay j is inherited by all earlier delays. If j>=2^P, finite pigeonhole
would make two of these distinct tails equal. This proves j<2^P without a
bound on the input delay or spatial transient. A separate finite-profile
argument proves that any eventually periodic temporal input reconstructs an
eventually periodic spatial row, so the unboundedness is genuinely in the
periods of periodic rows.

## Validation at the moving verifier pin

The five research modules replayed 22+17+62+44+28=173 declarations, including
generated declarations. The combined catalog and standalone essay sources
replay the same mathematics; their repeated checks are not counted as new
results. No nonstandard axioms or kernel shortcuts are used.

Initial cold core build plus full unchanged official checker replay passed
at `3eca23c0a9fa6b153313655e6d51835406c2d06e`, taking 44.6 seconds including
dependencies, with peak owned RSS 1.74 GiB. During this turn the verifier
moved to `0090056412733accaa27643d3cbbf982104f2251`, which incorporates our
earlier stripe-tail work. We merged that main commit normally into the PR
branch. The checker and this proof's imported sources are byte-identical
between pins. Incremental core build plus another **full** replay at the new
pin passed in 11.2 seconds. All five catalog headlines pass and all 173
declarations replay, with no new axioms. The standalone `Rule30Submission`
source also passes all 173 declarations at the current pin. Final research
build logs are empty; the unchanged checker emits its existing deprecation
warning. Historical repaired compile/setup failures remain in the logs.

## The evaluated essay draft

The [human-readable essay](work/essay-review.md), [notebook](work/delayed-defect-essay.nb)
and [embedded standalone source](work/Rule30Submission.lean) are ready for
review. The notebook carries the entire source as an icon, obtains the kit
from `RULE30PRIZE_KIT`, shows the single-seed pattern and center prefix,
computes delayed-defect previews, displays headline and lemma types, lists
standard axioms and invokes LeanLink full kernel replay.

A separate fresh plain kernel evaluated all seven input cells from the saved
notebook and passed the full 173-declaration replay. The source extracted
from its icon is byte-for-byte identical to the checked UTF-8 source,
including its final newline. All 805 plotted reconstruction cells match an
independent packed-bit calculation. Both PNGs were viewed. The local Windows
runner uses the existing official-source LeanLink bridge build; no new bridge
patch or bypass was introduced. Independent official Check.lean replay is
also recorded. The notebook itself contains no local bridge path or research
file dependency. Earlier DLL-loading, input-cell holding and newline issues
were repaired before this successful fresh evaluation.

**No prize API submission has been made.** Fresh human consent for this exact
essay is still required. [Pending-review metadata](PENDING-REVIEW.json) records
the exact notebook and source hashes. Local checks do not confer Wolfram's
Lean Verified, Human Verified or prize-award status.

## Finite experiments and their limits

An exact cyclic-preimage search reached 50,001 nodes and spatial period 112
before its node cap. All 49,997 new parent edges were independently checked.
An even-phase predecessor word of density 5/28 appears, but its boundary
compatibility is unproved. These cyclic whole-row predecessors form a
superset of valid Theta tails; this is neither a C4 counterexample nor an
actual finite-right witness. The raw graph's minimum field excludes its
four base words; including bases, the minimum is 1/7. The compressed graph
and a checked 360-edge witness path are retained.

Separately, 10,950 random prefixes satisfying four finite forbidden-word
constraints found no C4 candidate, with minimum sampled density 2/7. That
sampling missed the previously known 3/14 construction and supplies no
density floor. A structured delayed-defect search checked 537 cases,
recovered density 3/14 and observed many period-56 cycles, with no unresolved
cycle caps or C4 candidate. The uniform period theorem above does not infer
anything from these finite searches. They motivated and tested the mechanism.

No density bound, critical-charge inequality, absorption theorem or actual
finite-right realizability theorem follows. Those missing bridges, and the
full canonical higher-source parity, remain the relevant open work. Another
finite cycle census cannot supply them. All 450 selected hashes in nine
earlier archives are unchanged. All eighteen final guarded jobs exit normally.
