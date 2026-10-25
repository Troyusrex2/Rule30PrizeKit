# Uniform conservation proof sent upstream as catalog PR21

**Problem1 remains open.** The uniform integer conservation theorem from
[the earlier report](../20261025-greedy-and-conservation/REPORT.md) is now a
directly importable, core-only catalog module in
[upstream PR21](https://github.com/WolframInstitute/Rule30PrizeKit/pull/21).
The PR is open and ready for review; it has not been merged, accepted by a
maintainer, tagged by Wolfram or submitted as a new prize essay.

Contribution commit: `fc2ee3f3e17d7d356f296a279eed6acca70d36ca`, branch
`contribution/local-conservation-20261025`. It changes exactly three files:
the new736-line `Rule30LocalConservation.lean`, its public catalog import,
and its row in `lean/README.md`. The proof is consolidated from the six
checked research modules, with catalog namespaces and flat exported headlines.
The integer/four-step/cyclic-word scope is unchanged, and references and
the absence of a literature-novelty claim are retained in the module.

The new catalog form passed a real core-package Lake build and full unchanged
checker replay of all195 owned declarations and three headlines:

- `cyclic_conserved_iff_shift_coboundary`
- `local_conserved_iff_shift_coboundary`
- `Word.image_eq_four`

All are in namespace `Ruliology.CellularAutomata.Rule30LocalConservation`.
No new axioms or decision shortcuts occur. The new module builds without
warnings. Only the unchanged checker's existing replay deprecation warning
appears. Final build/check guard:5.47 seconds, sampled peak0.90GB owned RSS,
normal termination. The final build reused its compiled dependencies.

Reference pin: `3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean4.35.0.
Unchanged checker SHA-256:
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
Catalog source SHA-256:
`3633cdb7b76ecfd512fdeacf6078d02c844d6bd5b6f199f0a1fd517e2f021052`.
The exact source was read back from GitHub at that commit and byte-compared.
PR metadata/head/files/body were independently read back too. There are no
GitHub status checks listed; this is local verification, not a CI pass.

The root README links the PR for other agents. It is **not available in the
reference kit** until merged and the verifier image updates; current proofs
must still carry the source or use an owned local module.

To reproduce in a scratch kit at the pin, install the module in
`lean/Ruliology/CellularAutomata/` and run:

```
cd lean
lake build Ruliology.CellularAutomata.Rule30LocalConservation
lake env lean --run ../Check.lean Ruliology.CellularAutomata.Rule30LocalConservation --claim partial --headline Ruliology.CellularAutomata.Rule30LocalConservation.cyclic_conserved_iff_shift_coboundary --headline Ruliology.CellularAutomata.Rule30LocalConservation.local_conserved_iff_shift_coboundary --headline Ruliology.CellularAutomata.Rule30LocalConservation.Word.image_eq_four
```

`check_catalog.py` retains original paths for provenance. Its final checker
runs from the isolated core package, so Lake resolves the new catalog module
there. An initial attempt from the separate reference project's root resolved
the existing Ruliology package first and could not locate the new module;
the passing run fixes the environment without editing the checker or reference.

All39 hashes in the new causal block-cycle archive and79 hashes in the prior
conservation/frontier archive were checked before this catalog contribution.
No earlier archive or other session's files were changed. Human approval of
a specific fresh essay remains necessary before a new prize-API submission.
