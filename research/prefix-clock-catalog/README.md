# Whole-prefix clocks, finite front returns, and sharp escape from period 32

Partial results by Troy Lowry with OpenAI Codex. General individual-diagonal period nonloss, arbitrary-clock classification, homoclinic past closing, Q01, and the Rule 30 Prize problems remain open.

## Results

For every ordinary Rule 30 initial configuration white to the right of a boundary, the least dyadic periods of its entire right-diagonal prefixes form a monotone stay-or-double clock. Growth makes the newly added profile antiperiodic at the old prefix period. The guarded11011 exclusion follows from the RightProfiles shift law, with the actual-prefix hypotheses discharged.

The whole prefix through diagonal n has universal period `2^B(n)`, where the kit's existing `B(n)=ceil(n/2)+Q(0,floor(n/2))`. The DifferenceOrder/RecordCharge argument is reused with prefix clocks; its arithmetic is not claimed as new. For a finite nonzero seed with leftmost black cell L and white right boundary R, a whole-prefix period p>0 must satisfy `n<R-L+2p`. Its prefix exponents therefore eventually exceed every fixed exponent, with an explicit threshold.

A literal three-bit anchor embeds the kit's finite stripe-front dynamics in those right diagonals. For every width K, word W<2^K, and phase p<2,

    orb K (2^B(K+2)) (W,p) = (W,p).

This includes width zero. For positive K, the old general return `2^K` can be smaller at small widths; at K=40 the new bound is `2^24`. A previously certified particular cycle can already have a shorter return than either general bound. This concerns a finite front window, not infinite stripe-tail mortality.

A checked graph of 2116 pairs of32-periodic profiles yields all-depth low-clock results. For any actual right-bounded seed, if a prefix's exponent E is at most5, its last profile realizes that exact exponent and the following profile cannot drop below it. A first individual dyadic-period drop, if one exists, must follow a prefix clock of at least 64.

A rank certificate gives a sharper finite-clock obstruction: if diagonal n is not period two, the whole-prefix clock is at least 64 by diagonal n+14. This is uniform in n and in the initial configuration, including infinite left sides. The bound 14 is sharp: the actual finite seed 47649, supported at positions[-15,0], has prefix clock4 at diagonal3, while the entire prefix through diagonal16 still has period 32. A generic reverse-realization theorem connects the checked profile words to literal ordinary Rule 30 evolution, so sharpness is an actual-seed result.

Finally, if a rightmost black cell R exists, global period 32 of the whole right-diagonal array holds exactly when the initial left tail alternates from one cell left of R. Those two configurations already have global right-diagonal period 2. This is a bounded-clock classification of right-moving waves, not a statement about an ordinary vertical center column or about clocks64 and above.

## Catalog form and dependencies

The proposed catalog branch is stacked on ghywel's [PR51](https://github.com/WolframInstitute/Rule 30PrizeKit/pull/51), exact original commit `5d4cc975534cb09cd424646696de2488838afb52`; its RightProfiles source and authorship are preserved. The official base is `932cf8dde039b89b1dcbe9636867bb1b2057fef0`. Merge PR51 first. Its shift-law module is a dependency, not our contribution.

Nine main catalog modules are registered in Ruliology and the Added-in-the-kit table: RightPrefixClock, RightPrefixBound, FrontHalfPeriod, PrefixClockGrowth, ProfileGraph, ProfileGraphCases, ProfileClockEscape, ProfileClockSharpness, and LowClockWaves. Heavy graph/rank checks live under Rule30Certificates in ProfileGraph32 and ProfileClockRank32. Public theorem names remain stable across the data-module extraction.

The finite-front application was prompted by G.P.J.W. Quint and Gemini's [PR45](https://github.com/WolframInstitute/Rule 30PrizeKit/pull/45). It uses the already official FrontLift module and does not depend on PR45's unmerged module. The elementary orbit-return shift identity is also used there. Official half-rate and moving-edge proofs are credited in their source modules.

## Validation

The final LF catalog sources passed a fresh 33-source dependency-closure build and the unchanged official checker replayed **all 1101 owned declarations** across all 11 new modules, with 63 explicit headlines. Combined imports, theorem types, and axioms were checked. There were no reused objects, source warnings, or new axioms. Most of the declaration count consists of certificate helpers, not separate mathematical insights.

The successful integration took 152.31seconds and peaked at about1.84GiB owned RSS, within fixed 300-second/8GiB guards on G913. This is a focused dependency-closure build, not a whole-catalog build. These are local unchanged-checker results, not a claim of Wolfram reviewer approval.

Reproduce with Python and the exact recorded Lean4.35.0 Windows toolchain:

    python -B replay/verify.py --lean C:/path/to/toolchain/bin/lean.exe --out D:/new-empty-output

The verifier builds a fresh project, checks source/toolchain/checker hashes, replays every owned declaration in every new main/data module, and prints all headline types/axioms. All source inputs, build/check/type logs, guard receipt, and a byte manifest are included.

Earlier immutable archives retain [prefix/front/growth controls](https://github.com/Troyusrex2/Rule 30PrizeKit/tree/c1c5750d84a608083640e329a63a8aaa5ad90f3c/research/front-half-period) and [graph generation, independent literal audits, and failed decoder experiments](https://github.com/Troyusrex2/Rule 30PrizeKit/tree/57e602a712a771da55b2ae6e321581a5b1cc33db/research/periodic-profile-nonloss). Their numerical observations remain explicitly separate from the kernel proofs. This bundle is the final catalog layout, including the sharp escape bound and explicit wave classification.
