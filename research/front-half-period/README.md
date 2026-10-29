# Prefix clocks and universal stripe-front returns

Partial results, not a Rule 30 Prize solution. Submitted by Troy Lowry.

## Results

`Rule30RightPrefixClock` uses the least dyadic period of the **whole right-diagonal prefix**, rather than the least period of its last diagonal. For every initial configuration white to the right of a boundary, these exponents exist, stay or increase by one, and growth makes the newly added diagonal antiperiodic at the previous prefix period. The guarded `11011` exclusion applies to these actual prefix exponents when its base exponent is at least two. It does not assume individual-period nonloss.

`Rule30RightPrefixBound` supplies the hypotheses of the official kit's difference-order / record-charge argument using these prefix clocks. For any such right-bounded initial configuration, the entire prefix through diagonal n has period

    2^B(n),  B(n) = ceil(n/2) + Q(0,floor(n/2)).

Here Q and B are the existing `Rule30RecordCharge` definitions. The half-rate accounting is reused from the kit, not claimed as new arithmetic. The result allows arbitrary initial cells to the left, including infinite left sides.

`Rule30FrontHalfPeriod` embeds the kit's alternating finite front dynamics in ordinary right diagonals. For a front word W, the full initial code is `8W+5` in phase zero and `8W+3` in phase one. The three anchor bits evolve as `101 <-> 011` (ordinary binary, most significant bit first); their forcing reproduces both front phases exactly. For every K, W < 2^K, and p < 2,

    orb K (2^B(K+2)) (W,p) = (W,p).

The phase-zero embedding is proved bit by bit. The phase-one conclusion follows by moving around the kit's existing finite return orbit. Width zero is covered separately. The old universal return for positive K is `2^K`; for small K it can be smaller than this new bound. At K=40, the new bound is `2^24` rather than `2^40`. This is a bound on **finite front-window return**, not on extinction of an infinite stripe tail. It does not improve a particular previously checked cycle whose known period is already smaller.

`Rule30PrefixClockGrowth` complements the upper bound with the moving-left-edge obstruction. If the seed has leftmost black cell L and white right side beyond R, a prefix through diagonal n with period p > 0 must satisfy

    n < R - L + 2p.

At time p, right diagonal `-L+2p` meets the moving leftmost black cell; at time zero that diagonal lies strictly left of the seed and is white. This proves that the whole-prefix exponents eventually exceed every fixed exponent, with explicit threshold `(R-L).toNat + 2*2^e`. It uses the official finite-seed moving-edge theorem and does not assert that every individual diagonal retains the preceding diagonal's period. This is an elementary complement to the upper bound, not a claimed classification of all finite-seed periods.

## Dependencies and credit

Official kit pin: `932cf8dde039b89b1dcbe9636867bb1b2057fef0`.

The exact `Rule30RightProfiles` source comes from ghywel's [PR51](https://github.com/WolframInstitute/Rule30PrizeKit/pull/51), head `5d4cc975534cb09cd424646696de2488838afb52`. Its shift law supplies the prefix-word exclusion. That unmerged module is preserved with attribution and source hashes in this standalone replay; it is not represented as our contribution.

The front application was prompted by G.P.J.W. Quint and Gemini's stripe-structure [PR45](https://github.com/WolframInstitute/Rule30PrizeKit/pull/45), head `f481c02b3ebe80d66e2a7bf8214b8b720d087eb5`. The elementary orbit-return shift identity is also used there. The front proof imports the already official `Rule30ZeroBoundaryStripeFrontLift`, not PR45's new module. An independent fresh replay of PR45 passed all 153 declarations / 8 headlines separately; that audit is not an assertion that this new application has been reviewed by Wolfram.

The prefix-clock and upper-bound sources are byte-identical to the previously shared [prefix-clock archive](https://github.com/Troyusrex2/Rule30PrizeKit/tree/e1ff89b9cd0059082ea0126e35414dc8a4a11d9c/research/right-prefix-clock).

## Verification

The replay directory contains every source dependency, the unchanged official `Check.lean`, a source manifest, and a verifier that constructs a fresh project. It builds dependencies in sequence, replays **every owned declaration in all four new modules**, checks explicit headline types, prints axioms, and records source warnings. No objects are reused. This is a focused dependency-closure build, not a whole-catalog build. Exact counts and resource receipts are in `evidence/RESULT.json` and the guard receipt.

Reproduce with Python and the exact Lean 4.35.0 Windows toolchain identified by the manifest:

    python -B replay/verify.py --lean C:/path/to/toolchain/bin/lean.exe --out D:/new-empty-output

No external Python package is required by the verifier or controls. The verifier requires the recorded toolchain executable hash; source proofs themselves use ordinary core Lean. The unchanged official checker rejects new axioms and replays kernel declarations. The proof uses neither `sorry` nor computational axioms.

Independent numerical controls check both anchor phases for all 1024 ten-bit words and compare the bitwise front update with its literal Boolean recurrence. Complete cycle decompositions for widths 1 through 18 check all states, absence of transients, dyadic periods, and the proposed bound. These controls are evidence for the implementation, not substitutes for the Lean proof. Their source and receipt are included.

## Open problems

These results do not prove generic individual-diagonal period nonloss, homoclinic past closing, the absence of finite legal Gate rows, Q01, or any Prize conclusion. They provide bounds and a concrete connection between existing contributors' tools. A catalog integration should coordinate the dependency on PR51 rather than silently duplicate its author's module.
