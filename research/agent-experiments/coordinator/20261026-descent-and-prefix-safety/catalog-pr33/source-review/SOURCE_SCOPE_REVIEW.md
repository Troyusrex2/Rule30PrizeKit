# Cedar source and scope review

Verdict: source/scope PASS for the captured candidate below. No correctness or scope blocker found. This is a read-only source review, not an independent Lean build or kernel replay.

## Exact source

- Candidate: `D:/MWB/Rule30/finite-return-eight-catalog-20261026/lean/Ruliology/CellularAutomata/Rule30FiniteReturnEight.lean`
- Reviewed SHA-256: `005e100a7606c711d1e149d2b505bf74460be1468d74586f1c87bc4c504feafd` (395 lines).
- Requested SHA-256: `a6524c89b9f688a5dbf10fcdbe7e45ea7f843350f63b23857ac818f95767d73a`.
- Wolfram confirmed `005e100a...` as the final catalog hash after this review, explaining that the worker normalized mixed line endings without text/proof changes. The receipt is attached to the confirmed final bytes `005e100a...`; no claim is made about the unread earlier hash. The captured file and direct dependency copies accompany this receipt.

## Findings

1. **Orientation and simultaneous update:** `change p r (v :: vs)` recurses with the old `v,p`, so it is a parallel update. `asState xs = word xs.reverse` correctly converts older-first words into the catalog's newest-first state. `F_state` matches the literal `diagonal x k = xor (x k) (x (k+1) || x (k+2))`. The two white older boundary bits and the reverse-index boundary cases agree.
2. **Entire state, not a projection:** `F_state` is equality of functions `Nat -> Bool`. Its out-of-range branch covers every zero-tail coordinate, which remains zero under diagonal. `evolution_state` extends this equality through every iteration. There is no omitted newest-cell extension in this catalog map.
3. **Injectivity and truncation:** `word_injective_length` requires equal lengths, correctly avoiding the false claim that zero-tailed words are globally injective. `evolution_length` supplies that premise. Reversing an older-first `take (length-3)` gives newest-first `drop 3`; `word_drop` identifies that with the full shifted state `fun k => x (k+3)`.
4. **All widths and finite support:** the final theorem represents `x` by `(List.range W).map x` using the explicit white-tail hypothesis. `W` need not be minimal; empty states, widths below three, and trailing white cells are included. No normalization or nonzero-state hypothesis is smuggled in.
5. **Core certificate and clocks:** the 36-state, nine-time-profile certificate tracks the first two-step discrepancy and its delayed eight-step discrepancy. `run8_cons` is a definitional semantic bridge; induction covers every finite word. No Safety import, Safety-completeness assumption, least-period assumption, or pre-existing eight-step-return hypothesis is used to obtain the equivalence. The module contains no `sorry`, new axiom, or `native_decide`.

## Scope that must remain explicit

The conclusion is `iterate x 8 = x` iff the shifted finite-support state returns after two steps under the catalog's **triangular diagonal map**. Return after eight/two means period divides eight/two; it does not assert least period eight/two. Finite white support is essential to this proof. This is not a theorem about arbitrary infinite states, arbitrary controlled drivers, or the physical fixed-center Rule30 prize sequence, and does not settle D3 or the prize problem.

No candidate, dependency, shared reference, or production file was modified. No builds, tests, searches, API calls, or workers were launched for this review. Root's independent replay remains the separate compilation evidence.
