# Exact return-eight reduction and a conditional safe-output reader bridge

**The return criterion below is now proved for every finite word. Safety completeness, full reader separation and Prize Problem 1 remain open.**

`CedarReturnEightReduction.return_eight_iff_prefix_two` proves:

```lean
theorem return_eight_iff_prefix_two (xs : List Bool) :
  evolution 8 xs = xs ↔
    evolution 2 (xs.take (xs.length-3)) = xs.take (xs.length-3)
```

Evolution is the literal simultaneous older-first Rule 30 map with both missing older cells white. Thus deleting three newest cells turns the whole-word eight-step return question into a two-step return question. There is no safety premise, no supplied clock, and no width bound. Nat subtraction covers empty and short words. This is not a claim about arbitrary later clock doublings or a fixed physical observation column.

The proof uses thirty-six existing exact temporal profile pairs, grouped into four categories. A small kernel-checked certificate says that a first two-step discrepancy moves the profile into the first delayed category; the next two cells advance that category, and the following cell cannot return after eight updates. An induction on the actual word length connects this certificate to `run8` and then to literal evolution. No unbounded carry argument is assumed as a premise.

`CedarMarkerReturnTwo.return_two_iff_markers_zero` independently characterizes two-step return: the delayed `100` marker streams of both the original word and its one-step image must be all zero. Its proof is an all-width Boolean carry induction. Consecutive marker streams are disjoint, so equality of the streams is equivalent to both vanishing. The first three entries are zero; entry k+3 records the spatial marker starting at k. Together these two theorems give an explicit marker test on the shorter prefix.

## What safety completeness would supply to the reader

`PrizeSafetyBridge.safe_equal_reader` assumes the exact global hypothesis

    ReturnComplete := forall xs, Safe xs -> evolution 8 xs = xs.

Here Safe means that the newest temporal trace never has two successive zeroes. Under that hypothesis, two same-width words with the same all-time newest trace, safe on either side, are accepted by the previously sound seventeen-state reader. Consequently a safe-output pair in its sink state must eventually separate.

The proof combines the checked safety-language bridge with a finite product certificate: twenty-eight live single-word profile states on each side, 784 state pairs, and 1,024 live transitions. Every equal-profile accepted final pair is reader-accepted. The transition identities are checked in the kernel; a word-length induction handles arbitrary widths. The concrete product is not being substituted for a finite-width census.

This establishes the safe-output part of the connection between the two research routes. **ReturnComplete remains a hypothesis.** Equal unsafe traces, complete separation in the sink, the observer criterion and the physical-center problem are not settled. In particular, the separate condition that an equal newest trace with unequal parent traces must be safe is still an open boundary-sensitive target.

## Exact orientation matters in the height criterion

`RootOrientedHeight.safe_iff_oriented_height_range` completes the earlier necessary condition. For arbitrary drivers a,b and a child satisfying x(t+1)=x(t) XOR (a(t) OR b(t)), let Z(t) indicate that both drivers are zero, and H_Z(T)=sum_(t<T)(-1)^t Z(t). With q(0)=2[not x(0)]-1,

    Safe x  iff  H_Z(T) belongs to {0,-q(0)} for every T.

The reverse implication uses the exact signed event identity over integers: the two allowed height values force every marked event height to vanish, hence every temporal `00` event is absent. The module also checks a counterexample to dropping the initial orientation: constantly white drivers give unmarked height values {0,1}, but a constantly white child is unsafe. No genuine finite-white ancestry is inferred from a height bound alone.

## A failed reconstruction step, precisely scoped

`ResetExcursionControl.one_excursion_counterexample` checks two actual finite-white words, `100001000000` and `100001100000`. Their pair is in reader sink15; both newest traces begin `00010100`, and both have a three-white suffix at time6. Nevertheless their immediate-parent values differ at time2. Thus that single excursion between resets does not determine the parent segment. This is a finite kernel-checked control, not an all-time equal-trace pair or a refutation of sink separation.

The retained height diagnostic independently replays eleven saved genuine orbits and tests one precise counterexample query: width20, a cyclic32-step return, newest trace not returning at8, zero signed white-height drift, and span at most2. Z3 reports UNSAT in21.17 seconds. This does not prove any all-width or all-clock height obstruction; no expanded sweep followed.

## Verification and external progress

| New module | Independently root-replayed declarations |
|---|---:|
| CedarMarkerReturnTwo | 45 |
| CedarReturnEightReduction | 26 |
| PrizeSafetyBridge | 100 |
| ResetExcursionControl | 6 |
| RootOrientedHeight | 13 |

The total190 includes definitions and generated declarations. Root rebuilt/replayed the existing CommonPast100 and ColumnReader119 dependencies, and checked exact source/compiled hashes of its own previously replayed safety220 and height43 dependencies. No peer binaries were reused. This phase does not count those previously replayed dependencies as freshly replayed again. All selected headlines and full module replays passed without new axioms, using Lean4.35.0, pin `5473ffd075f63c9d626e63b8455805d4831b39ca`, and unchanged checker SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. Every new root job passed the300-second/8-GiB-owned/2-GiB-free guards. Cedar's sealed v04 delivery has409 independently verified hashes; selected sources and fresh root evidence are provided here.

An independent worker also audited the updated external [PR31](https://github.com/WolframInstitute/Rule30PrizeKit/pull/31), exact head `88dd51194cc4ae48bff5339418d33b54265330cb`: WhiteEndNine204 and PaddedWords14 declarations fully replayed, all eleven headlines accepted. The immutable112-hash audit is retained and root-checked; root did not run a second kernel replay of these external modules. This is work by @AIOvernight/Claude, not our mathematical novelty. The exclusion range remains q>=9. The revised proof supplies its own pumping argument from q=10 and a kernel q=9 base for the same formula; it also proves that pumping from nine fails. PaddedWords' bound9 integration passes. A dependency aggregate hit its300-second guard; completed artifacts were retained, and the remaining dependencies passed individual guarded jobs. The whole catalog/export build and additional PR-body search claims were not verified.

The public submission list now marks the corresponding external revision `R30-20261026-c389d5` Lean Verified. Our new results above have local independent kernel verification, not a new Wolfram backend evaluation. This research checkpoint creates no new catalog PR or prize essay/API submission and makes no prize-solution claim.
