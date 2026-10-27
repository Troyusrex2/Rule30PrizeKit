# Staggered-observer return lifting across three coordinates

This archive contains a proved return-lifting theorem for the official newest-first Rule 30 diagonal update. Let P>0 be even and let an older finite word u return after P steps. Prepend three arbitrary newer bits. If their actual orbit satisfies the all-time relation

    h0(t) = E(t) AND h1(t),

where hi(t) is coordinate i's own P-shift XOR defect and E is true on even times, then the extended word also returns after P. No whole-word clock for the extension or full-gate hypothesis is assumed. P need not be least or dyadic. The older word may be empty; its older continuation is white through the official `word` definition.

The final exact source is `bundle/sources/Rule30GatedDepthTwoResearch.lean`, SHA-256 `40320f742db353ee238fddd6d909c42cc15a74d4a4ce47ecb705bd98bff87362`. Its headline `word_staggered_three_return` is accompanied by the general actual-state bridge and the local depth-two exclusion. The complete authoritative types are in `bundle/prior-types/Rule30GatedDepthTwoResearch.log`.

## Verification status

The author's fresh leaf build and unchanged official full checker passed **70 own module constants, including 24 non-internal declarations and 46 internal generated constants, across 11 headlines**. There are no new axioms or source warnings. These are not 70 handwritten theorems. Author-run receipts are preserved in `evidence/author-attempt03/`.

The independent packager read the source, types, semantic bridge, mathematical papers and prior result, verified both author seals, and checked the exact eight-module official source closure at compatible pins 5473 and 7d665. This package was verified statically without another Lean build. No independent packager kernel replay, cold dependency build, Wolfram backend verification or human approval is claimed.

## Scope and prior work

The full-gated three-cell consequence was already implied by the prior verified `actual_even_two_plateau_or_clock_rigidity` theorem. It is not claimed as a new result here. The new proof addresses the different staggered defect relation and gives its direct return bridge. The prior argument uses a six-column strip; the new proof consumes eight columns. The exported local theorem retains the full `Actual` predicate. Neither a blanket strict generalization nor arbitrary-width transfer is asserted.

The stronger local paper removes the whole-output-clock premise of the first paper. It keeps q as an auxiliary profile and uses forward propagation rather than period-based backward transport. The original and strengthened papers are retained separately. The corrected author report is `paper/AUTHOR-REPORT-v02.md`; v1 is retained only with its explicit prose erratum. Under the marked relation, the global OR-defect identity is h1*(1+x0+E*x1); h1*(1+x0) is its odd-time specialization.

The all-time observer relation and the older tail's return remain hypotheses. There is no arbitrary-distance observer transfer, physical-center bridge, or solution of a Prize problem. See `SOURCE-TYPE-AUDIT.md` for exact quantifiers, orientation and boundary checks.

## Portable verification and reproduction

Static verification, without invoking Lean:

```text
python bundle/replay.py --verify-only
```

A future fresh replay requires Lean 4.35.0, the unchanged official `Check.lean` with SHA-256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`, and the recorded already-built official library. The eight official source snapshots and reference object hashes are in the bundle. The helper accepts explicit paths and creates a new output directory; no private research object is reused.

```text
python bundle/replay.py --lean PATH_TO_LEAN --official-lib PATH_TO_OFFICIAL_LIB --checker PATH_TO_CHECK_LEAN --output NEW_OWNED_OUTPUT_DIRECTORY
```

Run that command under an owned-process resource guard of at most 300 seconds and 8 GiB RSS, retaining at least 2 GiB system free memory. The helper's per-command timeout alone is not a substitute for the memory guard. It fully replays every constant and checks all eleven headlines, deriving fresh counts from returned results. Stored receipts are provenance, not a substitute for that future run. Do not write into the frozen archive or reference library.

The `prior-comparison/` source/report is retained for scope comparison only and is not part of the new module's build closure. The original paper argument and its strengthening came from the parallel prize-bridge research lane; the proof was formalized by the short-extension lane and independently source/type-audited while packaging. Credit remains Troy Lowry with OpenAI Codex.
