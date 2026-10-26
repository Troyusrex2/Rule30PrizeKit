# CedarPhysicalAgeBridge independent adoption audit

**Verdict: source/scope PASS. No semantic blocker found in the exact three-source delivery.** This is a source review, not a repeated build or checker replay. The coordinator owns independent formal validation.

Exact sources reviewed:

- `CedarPhysicalAgeBridge.lean`: `527ded7dc05fd3c1d11796bd5ed2435aa58e8f907df0303ec912b681a96252f8`.
- `PhysicalEarlyCases.lean`: `ea6daa684582f401e777aacfeccaf75984f2c4b0f12b822d08b1bb3919503c89`.
- `FrontBlackInterval.lean`: `6fbae106f9af8b3c8cba937c0a3f31071bf59e4664af530023fc2811d2c481da`, identical to the previously audited frozen source.

## Exact adopted scope

For n>=1, set L=20n, B=L+2^(L+1), N=2^B-1, W=N+9n, and Bphys=B+11n. In the pinned literal single-black-seed evolution `Rule30Jen.cell`, for every start time t, if the center is white at all times t+k with k<W, then for every j<n there exists a natural physical coordinate p with 1<=p<=Bphys and `cell (t+W+j) p=false`.

There is no premise on the following n center values, no periodicity or whole-state return premise, no nearest-front premise, and no black-anchor premise. The witness p may vary with j. `block_bound` specializes this to every nonempty list; its explicit following-driver-agreement and black-tick hypotheses are discarded because the physical theorem is stronger. The statement is conditional on the long white-center run; it does not assert such runs occur. This source does not establish padded-word exclusion, eventual center nonperiodicity, or a return/capture condition.

## Age, global reference, and causal transfer

`freeRow t D` keeps the **original** physical row `cell t` at and to the right of D, and sets every earlier integer coordinate to white. `freeEvol t D k` is its ordinary global Rule 30 evolution for k elapsed steps. Thus `front t D i k = freeEvol t D k (D-k+i)` has a genuine all-time triangular recurrence, proved by the full evolution rule and global white-left support induction. There is no replacement of an all-time recurrence by agreement on a finite protected strip.

`before_arrival` couples every positive coordinate through elapsed age N. Its only initial comparison is positive-coordinate equality; the center comparison at each boundary step uses the actual white-center premise and the global reference's support bound D-k>0. Negative physical coordinates need not agree. `after_cone` then transfers equality for all later elapsed s only at positions p>s. This is the ordinary radius-one dependency cone; it requires no later center assumption.

The aged interval theorem is applied at free elapsed age **N+s**, with s=9n+j. The reference is not reinitialized at N. Consequently the explicit onset N remains justified. Only the final white observation, at a position outside the center-influence cone, is transported to the physical evolution. This resolves the specific global-recurrence/future-clock concern raised in the earlier FrontBlackInterval review.

## Artificial anchor and backwards white prefix

The main theorem splits on `cell (t+N) 1`, rather than postulating a nearest black front.

If that bit is white, `white_back_pair` uses `rule false x y = x OR y`: white output with known white left predecessor forces both other predecessor bits white. `white_back_step` scans left to right using the white center, enlarging a white positive prefix of length m at the later time to length m+1 at the preceding time. Repeating N times from the singleton column1 gives original whiteness at positions1 through N+1. Hence D=N+2 is a valid artificial cut for `freeRow`, and the positive initial rows agree exactly. The bit at D can be either color. `front_recurrence` and the base interval theorem allow this; neither assumes that D is an actual black front.

For this choice D, the late-witness range N+2<=D<=N+11n-1 holds for every n>=1. No single-seed support-edge or front-existence theorem enters this branch.

## Coordinates and boundary cases

The free white witness has i in the closed interval [20n,B]. The physical coordinate is computed in integers:

`p = D - N - s + i`, where `s=9n+j` and `j<n`.

In the general `late_witness` range, D-N>=2 and s<=10n-1 give `p-s >= 2+20n-2(10n-1)=4`, so p>s strictly and p is positive. Its upper bound is at most B+2n-1, hence certainly at most the stated Bphys=B+11n. The conversion to `p.toNat` occurs only after positivity is proved, and conversion back uses nonnegativity. Time arithmetic identifies t+N+s exactly with t+W+j. No clipping or unsigned subtraction occurs in the physical coordinate.

The hypotheses n>=1 and j<n are essential to the stated arithmetic and are present at each public entry. In particular they ensure 20n>=1 before subtracting one to call the abstract interval theorem. The theorem does not claim n=0; the list wrapper explicitly requires positive length. There is no unsupported special case hidden at n=1.

## Early shield branch

If column1 is black at t+N, the pinned `black_stays` keeps it black throughout the next 9n white-center steps. `black_shield` then establishes the alternating stripe on physical columns1 through2n+1 at t+W. Odd positions are black and even positions white; `stripe_stationary` checks the correct Rule 30 orientation, including integer parity.

`stationary_cone` preserves that stripe on [1+j,2n+1-j] after j steps, without any boundary-driver assumption. The even position `p=n+n%2` lies in that interval for every j<n and remains white. The pinned black-shield hypothesis is a run of black column1, which has already been derived, rather than an extra premise. The extra distant-prefix helpers are sound but not used by the final two-case theorem.

## Evidence and remaining limit

The source hashes, equality of the copied early helper and its original, equality of the copied interval source and its audited original, and pinned local-rule/evolution/black-shield definitions were independently checked. `review.json` records the exact sources and comparisons. No worker receipt is counted as an independent replay by this review.

The mathematical composition is stronger than the earlier proposed free-marker argument: it never assumes a specific white marker survives after entering the center cone. It chooses a sufficiently distant aged reference witness and transfers that observation while it is still outside the cone. The remaining task is a separate exclusion/return argument; this review does not adopt the prospective `EXCLUSION_PAPER.md` proof or any later module.
