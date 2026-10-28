# Legal gates erase inverse-head choices

Developed by Troy Lowry with OpenAI Codex, 2026-10-28. Partial structural results; no prize or historical-priority claim.

For the official zero-wall evolution `Rule30ZeroBoundary.zrow`, write `a(t)=zrow L t 1` and `G(r)=NOT a(2r)`. The gate language has little-endian eight-bit words

    S = {8,9,16,18,33,36,66,72,132,144}.

Suppose the boundary is black at odd times and G is legal. The two possible heads of the first inverse agree from spatial depth **7** onward. With the prescribed first inverse fixed, the second inverse's two heads agree from depth **11** onward. More strongly, **all four two-step inverse histories agree from depth 20 onward**. The last statement needs only the first ten gate bits and the three overlapping S-windows they contain, together with twenty boundary ticks. None of these tail-agreement theorems assumes that L is finite.

Consequently, for finitely supported L in this gate class, either all four two-step inverses are finite or none is. Finding **any actual finite two-step predecessor** is equivalent to finiteness of the prescribed `back true (back true L)`. This removes the wrong-head obstruction within the class. It does **not** prove finite-predecessor existence, class emptiness, Q01, or Prize Problem 1.

The final extension also erases the inverse's initial **wall bit**, with agreement from depth 12. Thus an actual finite predecessor whose wall is black transfers to the prescribed white-wall inverse. `single_seed_left_inverse_finite` applies this to the actual single-seed left row at any positive age satisfying the local gate condition. It does not assert that those conditions hold at any particular age, or that repeatedly reconstructed predecessors retain actual single-seed ancestry.

The independent `Rule30InverseRunsResearch` module classifies first-inverse finiteness for arbitrary finite rows. Starting from a false flag, each zero-separated black run updates it by its length modulo three: 0 preserves, 1 resets false, 2 toggles. A final true flag characterizes a finite prescribed head-1 inverse. The formal run statement assumes an explicit block representation; the general scan criterion covers every support bound, including zero.

See [PROOF.md](PROOF.md) for the exact hypotheses and proof structure.

## Verification

The unchanged official checker passed after a **fresh ten-source build**, without reused objects:

| Module | Owned constants replayed | Headline statements |
|---|---:|---:|
| `Rule30GateInverseMergeResearch` | 166 | 15 |
| `Rule30InverseRunsResearch` | 109 | 3 |

Both proof sources and all eight official dependency sources built without warnings. All headline types matched, and no new axioms were found. No `sorry`, `native_decide`, `bv_decide`, or modified checker is used. Finite certificates are checked with kernel computation and connected by general proofs to the official dynamics and inverse functions.

The final owned-process guard exited 0 in 23.135 seconds, with approximately 1.83 GB peak owned RSS and 41.3 GB minimum free system memory. This is a fresh build of the stated ten-source closure, **not** the whole 141-module catalog. Final receipts and printed types are in [evidence/fresh10-final](evidence/fresh10-final/RESULT.json). The first fresh build of the 141-constant version remains separately labelled in `evidence/fresh10`; cached-dependency validations are in `evidence/reused`.

The official source/checker closure is byte-identical between the original validation pin `7d665044b904117af9e82328aeb90a30692b2b85` and current main `932cf8dde039b89b1dcbe9636867bb1b2057fef0`; see [MAIN-COMPATIBILITY.json](evidence/MAIN-COMPATIBILITY.json). The fresh build is pinned to the latter.

Reproduce with Python 3 and an existing Lean 4.35.0 installation:

```text
python verify.py --audit-only
python verify.py --lean /path/to/lean --out /a/new/output/directory
```

The verifier checks exact source/script hashes, refuses an existing output directory, builds the eight official dependencies and two proof modules into a new library, replays both modules with the unchanged `Check.lean`, and prints every selected type and axiom list. It needs only Python's standard library. The historical resource guard additionally used `psutil`.

`certificate/generate_history_certificate.py` regenerates the coalescence source from the retained base proof and extension plus twelve explicit finite tables; the generated source is written inside that directory. The checker verifies the tables rather than trusting Python's calculation. The Lean theorem `gate_prefix_coverage` exhaustively proves that the twelve tables cover every legal ten-bit prefix, not merely sampled periodic gates.

## Related work and limits

The official [Rule30PrefixMerger](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PrefixMerger.lean), incorporated through PR 42, proves a related seven-cell rewrite and locality of an initial free-bit edit under its stated two-black-free-bit hypothesis. The present modules use the official zero-boundary core directly; they prove inverse-head coalescence for the specified gate language and the resulting actual-predecessor equivalences. The related result is not an extra premise or a claimed contribution of this archive.

Generic rows can have a finite predecessor while a prescribed head fails. The new theorem removes that distinction under the stated gate-window hypotheses. It does not establish that an arbitrary legal gate has a finite spatial realization. The higher-history and tail-equivalence conjectures remain open; no inference from finite experiments is used as a Lean premise.
