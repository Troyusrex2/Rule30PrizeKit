# Legal gates erase inverse-head choices

Developed by Troy Lowry with OpenAI Codex, 2026-10-28. Partial structural results; no prize or historical-priority claim.

For the official zero-wall evolution `Rule30ZeroBoundary.zrow`, write `a(t)=zrow L t 1` and `G(r)=NOT a(2r)`. The gate language has little-endian eight-bit words

    S = {8,9,16,18,33,36,66,72,132,144}.

Suppose the boundary is black at odd times and G is legal. The two possible heads of the first inverse agree from spatial depth **7** onward. With the prescribed first inverse fixed, the second inverse's two heads agree from depth **11** onward. More strongly, **all four two-step inverse histories agree from depth 20 onward**. The last statement needs only the first ten gate bits and the three overlapping S-windows they contain, together with twenty boundary ticks. None of these tail-agreement theorems assumes that L is finite.

Consequently, for finitely supported L in this gate class, either all four two-step inverses are finite or none is. Finding **any actual finite two-step predecessor** is equivalent to finiteness of the prescribed `back true (back true L)`. This removes the wrong-head obstruction within the class. It does **not** prove finite-predecessor existence, class emptiness, Q01, or Prize Problem 1.

The final extension also erases the inverse's initial **wall bit**, with agreement from depth 12. Thus an actual finite predecessor whose wall is black transfers to the prescribed white-wall inverse. `single_seed_left_inverse_finite` applies this to the actual single-seed left row at any positive age satisfying the local gate condition. It does not assert that those conditions hold at any particular age, or that repeatedly reconstructed predecessors retain actual single-seed ancestry.

The independent `Rule30InverseRunsResearch` module classifies first-inverse finiteness for arbitrary finite rows. Starting from a false flag, each zero-separated black run updates it by its length modulo three: 0 preserves, 1 resets false, 2 toggles. A final true flag characterizes a finite prescribed head-1 inverse. The formal run statement assumes an explicit block representation; the general scan criterion covers every support bound, including zero.

`Rule30GatePastThreeResearch` proves a further finite-prefix editing result for an **arbitrary infinite shared future**. Two admissible three-bit gate pasts reconstruct equal spatial rows at every depth >=20, so either both reconstructions have finite support or neither does. It checks the six inverse layers jointly, not just the final row. This fixes the edited past length to three; it does not establish the conjecture for arbitrarily long pasts.

See [PROOF.md](PROOF.md) for the exact hypotheses and proof structure.

## Verification

The unchanged official checker passed after a **fresh eleven-source build**, without reused objects:

| Module | Owned constants replayed | Headline statements |
|---|---:|---:|
| `Rule30GateInverseMergeResearch` | 166 | 15 |
| `Rule30InverseRunsResearch` | 109 | 3 |
| `Rule30GatePastThreeResearch` | 52 | 6 |

All three proof sources and all eight official dependency sources built without warnings. All headline types matched, and no new axioms were found. No `sorry`, `native_decide`, `bv_decide`, or modified checker is used. Finite certificates are checked with kernel computation and connected by general proofs to the official dynamics and inverse functions.

Final receipts and printed types are in [evidence/fresh11](evidence/fresh11/RESULT.json). This is the stated eleven-source closure, **not** the whole 141-module catalog. The earlier two-module and 141-constant builds remain separately labelled in `evidence/fresh10-final` and `evidence/fresh10`; cached-dependency validations are in `evidence/reused`.

The [canonical catalog adaptation](canonical/README.md) also passed a fresh eleven-source Lake build, all three unchanged-checker replays, and a combined import smoke. It changes module/import names and line endings, with proof bodies preserved.

The official source/checker closure is byte-identical between the original validation pin `7d665044b904117af9e82328aeb90a30692b2b85` and current main `932cf8dde039b89b1dcbe9636867bb1b2057fef0`; see [MAIN-COMPATIBILITY.json](evidence/MAIN-COMPATIBILITY.json). The fresh build is pinned to the latter.

Reproduce with Python 3 and an existing Lean 4.35.0 installation:

```text
python verify.py --audit-only
python verify.py --lean /path/to/lean --out /a/new/output/directory
```

The verifier checks exact source/script hashes, refuses an existing output directory, builds the eight official dependencies and three proof modules into a new library, replays all three modules with the unchanged `Check.lean`, and prints every selected type and axiom list. It needs only Python's standard library. The historical resource guard additionally used `psutil`.

`certificate/generate_history_certificate.py` regenerates the coalescence source from the retained base proof and extensions plus twelve explicit finite tables; the generated source is written inside that directory. Running `certificate/generate_past_three.py` afterward regenerates the three-past proof, using the first generator's table output. The checker verifies the tables rather than trusting Python's calculation. The Lean theorem `gate_prefix_coverage` exhaustively proves that the twelve tables cover every legal ten-bit prefix, not merely sampled periodic gates.

## Related work and limits

The official [Rule30PrefixMerger](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PrefixMerger.lean), incorporated through PR 42, proves a related seven-cell rewrite and locality of an initial free-bit edit under its stated two-black-free-bit hypothesis. The present modules use the official zero-boundary core directly; they prove inverse-head coalescence for the specified gate language and the resulting actual-predecessor equivalences. The related result is not an extra premise or a claimed contribution of this archive.

Generic rows can have a finite predecessor while a prescribed head fails. The new theorem removes that distinction under the stated gate-window hypotheses. It does not establish that an arbitrary legal gate has a finite spatial realization. The higher-history and tail-equivalence conjectures remain open; no inference from finite experiments is used as a Lean premise.
