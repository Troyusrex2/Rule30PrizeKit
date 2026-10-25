For every actual single-seed age pair `U > V`, an initially supported auxiliary field satisfying the divided-difference update and the common-gauge constraint for all time has a single phase outside the younger right front:

`h(t,p) = h(0,U) && cell(U+t,p)` whenever `p > V+t`.

The finite-horizon version needs the common-gauge constraints through `t + floor((U+t-p)/2)` and an initial upper support bound. The supporting half-line theorem classifies every initially subset common mode over a zero background as zero or the actual background. The auxiliary field is never assumed to be a physical Rule30 history. The proof adapts the catalog's XOR-rigidity gap argument with a black right endpoint; the canonical corollary embeds the exact region where the younger background vanishes.

Adds one core-only catalog module, its root import and catalog row. This does not prove the center observer, backward closure in the overlapping region, or Prize Problem 1. The unrelated bounded experiments are excluded from this PR.

Validation at reference commit `0090056412733accaa27643d3cbbf982104f2251`: core Lake build and unchanged official checker pass, including full kernel replay of all 95 declarations and four headlines, with no new axioms. Combined validation took 6.72 seconds and peaked at 833 MB owned-tree RSS. Independent scalar/exhaustive controls cover 87,380 initial pairs and 128,584 distance implications, with controls for the required black endpoint and time horizon.
