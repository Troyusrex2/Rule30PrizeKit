# External PR31: source and scope review

Audited exact head `88dd51194cc4ae48bff5339418d33b54265330cb` of AIOvernight/Rule30PrizeKit, submitted as https://github.com/WolframInstitute/Rule30PrizeKit/pull/31. The public source is external work; this receipt claims independent review and verification only. This audit supersedes the older head `16250824c5e80964495ca5ba6bb82fa69394a35a` only for the two exact modules identified below.

Source/scope verdict: **PASS**, with the important distinction between a common certificate formula and the pumping threshold recorded below. Formal replay results are in `AUDIT.json` and the raw logs, rather than inferred from this source review.

## Exact bytes and provenance

- `Rule30WhiteEndNine.lean`: SHA256 `25f485f20667a973c0b2960a0cffda4a2e7cf59121f8d6873ac6d265abe5b6ff`; Git blob `343b3e06b5bea7a2fdebaedbdcd50e21552efb6d`; 45,905 bytes.
- `Rule30PaddedWords.lean`: SHA256 `d2072051c4be3121de1e311dd340d471b0500e1020de66a0271daecc4b93408c`; Git blob `7c0cce3d8bcf93fc20c452773b935bb96241236a`; 5,150 bytes.

Both were fetched through the GitHub connector with the exact commit ref and base64 decoding, preserving source bytes. The Git blob SHA1 was recomputed independently and matches the API value. Saved PR metadata records the title and update time `2026-10-26T19:08:44Z`; mutable PR metadata is context, while the exact commit and hashes identify the proof under review.

## Pumping and the base case

`modeCert_white_end` uses the same expression for every `q >= 9`: width 12, five warm-up periods, distinguished phase 2, reachable set `reach 12 5 q`, intersected with fixed `lab0` and `lab1` masks. Its proof splits `q = 9` from `q >= 10`.

- `modeCert_nine` checks that expression at exactly nine white cells using `decide +kernel`.
- `pumpCheck_12` checks `pumpCheck 12 10 5 = true` using `decide +kernel`.
- `modeCert_pumped` is the general proof: for all `K M k q`, with `2 <= M`, `M <= q`, and a successful finite `pumpCheck`, the q-dependent mode certificate holds. White-step closure and monotonicity provide every extra white step; this is not a bounded scan over q.
- `pumpCheck_12_nine` checks `pumpCheck 12 9 5 = false` in the kernel. Therefore this is **not** a single successful pumping check starting at nine. The header and PR body explain this distinction accurately, although the short title alone can be read too broadly.

`closeW` has a bounded computational fuel, but its convergence is not trusted or assumed: `pumpCheck` explicitly verifies the resulting set's closure. `period_sub` uses the checked M-step containment and that closure for arbitrary additional steps. `chain_sub` then handles all five warm-up periods. The last closed set lies in `lab0`, giving both label-transition checks for the pumped cases. The base case permits label 1 and checks the two transition conditions directly.

## Semantic bridge

`fimage_mem` proves inclusion of every actual `stripStep K a z r` successor, for either arbitrary right boundary bit z. Its forward soundness, together with monotonicity, suffices; the exclusion theorem does not need a claimed equality of bitset images or an unproved reachability converse.

`enc_fapply` and `enc_fiter` connect these bitsets to the official `Enc` relation and literal single-seed `Rule30Jen.cell` evolution. The start set is all width-K strips, so the proof imposes no artificial initial strip or right boundary condition. `not_eventually_word_mode` starts from the official `EventuallyWord w`, whose definition is an arbitrary transient T followed by the literal center column repeating w. The required positive word length and K >= 1 are explicit and supplied by the final application.

The mode-certificate proof keeps every actual period-start strip in S0, reads the next column at each white phase, and uses the label transitions 1 -> 0 and 00 -> 0 to prove eventual period two in the sequence of distinguished labels. At the other white phases the column is forced; at black phases the OR of center and next column is already true. This yields eventual period `2 * w.length` for `orCol 0`, contradicting the official MaskedJen theorem under the assumed center periodicity. The arbitrary transient is preserved throughout.

The new main module imports only `Rule30StripCertificates` and `Rule30MaskedJen`. Its transitive Ruliology graph also contains the official `Rule30Prize` and `Rule30Jen`; there is no `Rule30WhiteEnd` or separate certificate-data import.

## Padded-word integration

The exact diff against official pin5473 is preserved in `padded-words-versus-official.diff`. The only functional edits are the new main-module import, the single-tail bound changing from ten to nine, the corresponding premise on `not_eventuallyWord_zeros_one`, and its invocation of the new theorem.

`paddedBound [true]` is literally 9. `eventuallyWord_swap` uses the official finite-seed realization and word rotation theorem to convert `0^q 1` into `1 0^q`; its positivity premise is discharged by the trailing one. `no_padded_word` invokes this result in its `[true]` branch. Existing bounds for the other tails and the `u.length <= 6` restriction remain unchanged. The description of a least bound is a statement about what this catalog proves, not a proof of optimality of nine.

## Limits

This verifies exclusion of eventual repetitions `1 0^q` for every q >= 9, their rotations used in the padded-word wrapper, and the wrapper's stated short-tail family. It does not prove the full Rule 30 nonperiodicity prize, ReturnComplete, D3, finite-white safe ancestry completeness, or exclusion of arbitrary mixed white-run words.

The PR body's additional search claims about mixed-gap codebooks, widths through 22, label-state counts, and limitations of q-independent sets were not adopted as formal results in this audit. No new theorem was developed and no public source was edited. No publication or submission was made by this reviewer.
