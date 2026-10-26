For every finite white-tailed triangular state, whole-state return after eight updates is equivalent to return after two updates after removing the three newest cells:

```lean
theorem iterate_finite_return_eight_iff (x : Rule30ControlledResponse.State)
    (W : Nat) (hx : ∀ k, W ≤ k → x k = false) :
    Rule30ControlledResponse.iterate x 8 = x ↔
      Rule30ControlledResponse.iterate (fun k => x (k + 3)) 2 = (fun k => x (k + 3))
```

`iterate_word_return_eight_iff` gives the finite-word version using `drop 3`. Both cover every width, including zero and short words, without a safety or supplied-clock hypothesis. The proof uses a 36-pair temporal-profile certificate and induction on word length. `evolution_state` connects the older-first proof representation to the catalog's newest-first map; same-length injectivity preserves whole-state equality through that bridge.

Adds one core Lean module, its catalog import and credited README row, and updates the module count. This is a finite-support triangular-state result; it does not establish nonperiodicity of the physical center column.

Validation at official pin `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0:

- Independent fresh build and unchanged `Check.lean` replay: **128 declarations, all four README headlines, no new axioms**; 2.29 seconds, 0.76 GiB peak owned memory.
- Cold `lake build Ruliology.CellularAutomata.Rule30FiniteReturnEight` in the unchanged pinned core Lean subproject: passed, including all eight official source dependencies; 10.56 seconds, 0.73 GiB peak owned memory.
- Independent source/scope review checked orientation, white boundaries, short words, truncation and full-state equality. `git diff --check` passed; the complete catalog import closure resolves to 125 modules.
- The full historical catalog-root build was not rerun.

Exact module SHA256: `005e100a7606c711d1e149d2b505bf74460be1468d74586f1c87bc4c504feafd`.

Developed by Troy Lowry with Cedar and OpenAI Codex. The underlying research proof and its scope are public in the [verified research checkpoint](https://github.com/Troyusrex2/Rule30PrizeKit/blob/0cbc49ef30888b32760def46ec31f954626192ff/research/agent-experiments/coordinator/20261026-return-eight-and-reader-bridge/REPORT.md).
