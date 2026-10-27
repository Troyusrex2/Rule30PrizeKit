# Independent audit: uniform local birth-potential obstruction

**Mathematical source, printed types, and final receipt: PASS.** This was a static review, with no Lean/Wolfram execution, new trajectory calculation, or proof-source modification.

Reviewed source: `Rule30LocalBirthPotentialResearch.lean`, SHA256 `369377cab23bff97d686bcf9441be04069bede425b8d28ac2494b4e5c0bba984`, from `local-birth-potential-formal-20261027T0745`. Final attempt03 records a full unchanged-checker PASS for **45 constants and seven named headlines**, with no new axioms. All 66 author payload hashes match manifest `b298610917ebda64bdebe2d4f7b1ce779ee73df497d83c8661082ea62b29b21c`. A packaging qualification appears below.

## Uniform mathematical argument

The theorem quantifies over every natural radius R. It excludes an integer-valued function E of exactly two physical windows on positions -R through R, taken at times t and t-4, together with t modulo 4. The required inequality would hold for every finite nonzero initial row and every t at least 4 whose center alternates in the specified absolute phase on [t-4,t+1]. Its birth cost is 1 exactly when the right-neighbor backward-four mismatch changes from false to true.

For each arbitrary R, the source cuts the previously verified periodic initial row to the closed interval [-(R+20),R+20]. The exterior is explicitly white, and the cell at -1 is black, proving `FiniteNonzero`. This is a symbolic construction for all R, not a collection of checked radii.

The official evolution is `Rule30Realization.evol`, whose update uses physical left, center, and right sites p-1, p, p+1 in that order. `evol_orbit` identifies it with the canonical integer-time periodic orbit by induction and the canonical physical recurrence. The official `Rule30ZeroBoundaryBarriers.evol_local` is used in the correct equality direction: the cutoff agrees with the periodic row initially on the padding interval, hence their evolutions agree inside the shrinking light cone.

`cut_agrees` covers all s at most 16 and all positions from -(R+1) through R+1. Indeed, the largest required cone extends only to R+17 in absolute position, within R+20. Consequently physical site 1 is covered even when R=0 and the observation itself contains only site 0. This separately justifies the birth readings, rather than assuming that birth is determined by a radius-zero observation.

Every local alternating-center premise used at source steps t=4,...,15 follows from actual finite-row agreement through time 16. Its lower endpoint t-4 is nonnegative. At observation time 16 the older row is time 12; at time 4 it is time 0. The canonical six-periodicity gives equality of both windows at these two observation times, and 16 and 4 have the same phase modulo 4. Thus `cut_observation_loop` proves equality of the entire observations, not merely the center values.

`cut_true_births` proves births at 4 and 10, with second readings at 5 and 11. The final contradiction needs only the first: the assumed inequality at 4 gives E(O5)+1 <= E(O4). All steps 5 through 15 are nonincreasing because the cost is either 0 or 1. The induction ends at E(O16) <= E(O5), contradicting O16=O4. There is no omitted step at 16, no Nat-subtraction truncation at a used birth, and no assumption that the full finite state returns. Integer order suffices; nonnegativity of E is unnecessary.

## Precise scope

The formal codomain is **Int**. The paper's analogous real-valued argument is mathematically valid but is not a separately Lean-checked theorem in this source. The printed headline suppresses some inferred types, so the codomain was checked directly in the source definition and theorem binder.

The potential may depend on R through the choice of E, but its time-varying input is exactly the stated observation. A support bound, full row, initial configuration, absolute unbounded time, or unbounded ancestry record is not an extra input to E. The witness gives only the finite alternating-center interval needed by the inequality. It does not give an all-time periodic center for the finite cutoff, and it is not asserted to be an age of the single black seed.

Accordingly, the theorem does not exclude inequalities restricted to actual single-seed histories, requiring an infinite periodic future, or using data beyond the fixed observation. It supplies no Prize Problem 1 conclusion and no counterexample to such stronger hypotheses.

## Evidence and dependency provenance

The frozen top-level source equals the attempt03 source snapshot. Its source/object/type hashes match the receipt, the source build log is empty, and the raw checker JSON equals the saved checker result. All seven reported headlines succeeded; all reported non-internal declarations use only standard axioms. The known checker replay deprecation warning remains in raw output. The checker bytes match SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

All ten official dependency sources equal their Git blobs at pin `7d665044b904117af9e82328aeb90a30692b2b85`. The eleventh dependency is the already reviewed canonical periodic counterexample, SHA256 `feb16ec4ddd636f751a5984d23093d18409355df1c8d38f594b5a151774f9632`. All eleven dependency object hashes and copied companion-object bytes match their stated origins.

Jen, Prize, and the canonical counterexample were copied from the root's fresh three-source validation. Its receipt is retained byte-for-byte, including the two official-dependency submission-metadata rejections despite successful kernel replay. Eight additional official locality dependencies were freshly compiled in the owned attempt02 closure and reused unchanged for attempt03. They were not all separately kernel-replayed in this worker run. The full 45/7 PASS belongs to the new leaf; this is not a fresh twelve-module replay claim.

The preserved attempt01 failure concerns a missing copied companion object, before the new source was checked. Attempt02 built the eight dependencies and then failed on a conditional-expression elaboration. Attempt03 uses explicit conditional-equality lemmas and passes. No checker modification, nonstandard axiom, or native decision procedure is introduced.

## Packaging-only qualification

The author report says compiled binaries were excluded from the seal, but its manifest includes 16 `.ir` and `.ir.sig` payloads under `attempt02/lib`; the inspected IR has a binary `olean` header. This does not affect the mathematical evidence. Preserve the author seal and omit these files from a source-and-receipt portable archive, with an explicit exclusion record. The archive preparer acknowledged this correction. No proof or build change is requested.
