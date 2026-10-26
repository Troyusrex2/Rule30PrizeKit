# Strict descent and a stronger returning-prefix theorem

Nine research modules passed independent fresh compilation and full replay through the unchanged official checker: 398 declarations, including definitions and generated declarations. This is progress on the finite-white safety problem. ReturnComplete, D3, full reader completeness, and Prize Problem 1 remain open.

The states here are genuine finite words with an older white boundary, evolved by the exact triangular Rule 30 map. `Safe` means that the newest temporal trace never has consecutive whites. `F8` means return of the **whole word** after eight updates. These are not statements about the fixed physical center column.

The main advances are:

- **Height-one descent without a supplied clock.** For any finite word whose newest signed white-height remains in an interval of width one, failure of whole-word F8 produces a genuine Safe/nonreturning word exactly one cell shorter. The witness flips the initial newest bit of the immediate older prefix. This remains valid when the visible newest column already has a small period: the proof retains whole-prefix equality throughout. See [HeightOneDescent](sources/HeightOneDescent.lean), `height_one_nonreturn_shorter`.
- **A stronger short-extension theorem.** If a prefix returns as a whole after eight steps and an extension of at most three cells is Safe, the entire extension returns after eight steps. The prefix itself need not be Safe. A kernel-checked certificate covers all 36 returning boundary pairs and all 15 short suffixes, followed by induction over arbitrary prefix length. See [RootReturningPrefixSafety](sources/RootReturningPrefixSafety.lean), `returning_prefix_safe_extension`.
- **An exact minimum-width obstruction.** Under safety completeness at every strictly smaller width, each proper prefix within three cells of a Safe/nonreturning word has both a temporal 00 occurrence and a temporal 11 occurrence. These are separate existential events, with no assertion that they occur together or within a fixed window. Leaf complementation requires completeness over all shorter words, not merely the original word's prefixes. See [RootMinimalCounterexample](sources/RootMinimalCounterexample.lean), `near_prefix_both_events`.
- **Height-two descent with an explicit parent condition.** A returning prefix extended by at most two cells must still return if the actual newest white-height remains in a band of width two. Consequently, a height-two whole-word nonreturn with a coSafe ancestor one or two cells back produces a strictly shorter Safe/nonreturning word. Here coSafe means absence of consecutive blacks. Under the stated smaller-Safe-word completeness hypothesis, both immediate nonempty ancestors must therefore have a temporal 11 occurrence. See [HeightTwoNearReturn](sources/HeightTwoNearReturn.lean) and [HeightTwoDescent](sources/HeightTwoDescent.lean).

For a trace b, the white height is H(T) = sum over t < T of (-1)^t times the indicator that b(t) is white. All-time band hypotheses are literal. The closed-period adapters explicitly require a positive even **column** period, zero drift, and the finite-window bound before deriving an all-time band. The height-one result also proves existence of a suitable even column period from the actual finite-white evolution, so its final theorem needs no external clock premise.

The height-one proof combines the genuine forbidden pattern 11011 with the height bound to isolate transitions. Three shared predecessor recurrences force two actual parent traces to coincide with the derivative. A 36-state return certificate is used only after assuming the shorter word returns; it is not an unconditional assertion that all twins have small period. The new height-two certificate covers 252 fixed boundary/suffix cases and then arbitrary prefixes. Neither proof is an increasing-width census.

## Validation and provenance

All nine modules passed the unchanged checker at kit commit `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0. Each run checked every new declaration and all requested headlines, with no new axioms. Successful guarded runs took about 3.5–7.4 seconds and at most 1.30 GiB of owned memory. [summary.json](summary.json), [formal receipts](formal), and [guard evidence](evidence) record exact source hashes and results.

The root verifier used its own previously replayed, hash-checked dependency artifacts; no worker binaries were used. Eight older dependencies contain 448 previously replayed declarations and were not rebuilt in this root batch. The height-two worker independently rebuilt its nine dependencies as well. Both sealed worker bundles were audited in full: 59 and 94 artifact hashes. An independent agent reviewed the root's stronger prefix theorem and its minimum-width consequence; [that review](work/prefix-source-review/REVIEW.md) found no gap. These are local kernel checks and agent reviews, not Wolfram human evaluation.

The exact finite-state return criterion was also packaged for the official catalog in [PR #33](https://github.com/WolframInstitute/Rule30PrizeKit/pull/33), head `4275be38012cbf7b8a8e578162371262e299f1e9`. Its separate independent replay passed 128 declarations/four headlines, and a cold normal Lake module build passed with all eight official dependencies. Its [validation evidence](catalog-pr33/final-validation.json) is included here. The full historical catalog-root build was not repeated.

## Remaining proof gaps

An arbitrary Safe/nonreturning word has not been shown to yield an actual height-two ancestor. The known anti-periodic height bound requires a specific adjacent periodic/anti-periodic pair; a general finite-word clock does not supply that pair at the Safe endpoint. A zero-forcing gate is also not automatically the trace of an actual column.

Within height two, the case where both parents have consecutive blacks remains unresolved. Smaller-width completeness for Safe words cannot be inferred merely by choosing a minimum-width height-two word. Current symbolic work explores that case with both minimality notions kept separate.

Even a proof of the finite-white safety classification would still need the outstanding reader/observer arguments connecting this research route to the physical center. No prize solution or new Wolfram API essay is claimed or submitted by this checkpoint.

Developed by Troy Lowry with Cedar and OpenAI Codex. The preceding [return criterion and reader bridge checkpoint](../20261026-return-eight-and-reader-bridge/REPORT.md) remains unchanged; all 4,044 owned artifact hashes in 47 earlier archives were verified before this archive was prepared.
