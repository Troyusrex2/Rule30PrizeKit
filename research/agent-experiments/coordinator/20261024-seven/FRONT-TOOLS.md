# General stripe-front tools in the catalog

[Upstream PR #16](https://github.com/WolframInstitute/Rule30PrizeKit/pull/16)
adds four core Lean modules on branch `research/stripe-front-tools-20261024`,
commit `9e72ac6`. It is independent of the tail-13 data contribution in
[PR #15](https://github.com/WolframInstitute/Rule30PrizeKit/pull/15).

- `Rule30ZeroBoundaryStripeFrontLift`: width projection and punctured-cycle
  lifting, with explicit higher-period and exceptional-witness hypotheses.
- `Rule30ZeroBoundaryStripeFrontPeriod`: highest-bit flip, period doubling,
  and the uniform return period `2^w` for every fitting width-`w` window,
  `w >= 1`, and phase zero or one. This proves return, not witness success.
- `Rule30ZeroBoundaryStripeFrontParallel`: correctness of parallel upper
  windows above a shared lower window, for all times and fitting lanes.
- `Rule30ZeroBoundaryStripeFrontReturnMap`: composition of finite upper
  return maps with a lower punctured certificate, checking only the exceptional
  residues along the finite return-map orbit. The cycle and witness checks
  are explicit assumptions; arbitrary-tail success is not claimed.

Each source follows the core catalog module format and uses the existing
stripe-front definitions and lane patterns. There are no new certificate
tables or dependencies. The umbrella imports and **Added in the kit** rows
are included. Developed by Troy Lowry with OpenAI Codex.

At reference `3eca23c0a9fa6b153313655e6d51835406c2d06e`, all four normal module
builds passed, followed by full kernel replay with the unchanged official
checker: **225 declarations, 42 headline lemmas, standard axioms only**.
The complete **125-job `lake build Ruliology`** also passed (7.891 seconds
with existing dependency build artifacts).

`front-tools-catalog-manifest.json` records the exact catalog source hashes.
`front-tools-catalog-evidence/` holds the four full reports, the aggregate
report, and umbrella build evidence. To regenerate in a separate checkout
at the reference commit, `prepare_front_tools_catalog.py` writes only the
four owned modules, their umbrella imports and catalog rows; then
`verify_front_tools_catalog.py` runs each normal build and full replay.
The scripts' default worktree is `front-tools-catalog-20261024` beside this
research checkout; adjust that local path when reproducing elsewhere.

The [checked research example](COMPRESSED.md) uses these tools to replace
the long tail-13 orbit check with a parallel return-map certificate. It proves
the same family and is not a solution of Q01 or Problem 1.
