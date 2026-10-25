For every positive window width, this adds a core Lean classification of integer densities conserved by four Rule 30 steps on all closed walks of overlapping input windows: they are exactly constants plus shift coboundaries. The cyclic hypothesis does not require a supplied local current; the proof constructs it. The converse is included, so the classification also covers all telescoping boundary scores.

The proof realizes arbitrary interior output words with a white trailing input, varies the two outer bits to force zero mixed endpoint difference, and shortens the density while preserving conservation. Induction reduces to the one-cell case. `Word.image_eq_four` connects the finite-word map to four updates of the official Rule 30 rule.

The module exports `cyclic_conserved_iff_shift_coboundary` and `local_conserved_iff_shift_coboundary`, and is imported and listed in the catalog. It uses core Lean only. This is a direct formalization for the stated integer/four-step class; no literature novelty, general ranking obstruction, real-valued classification or prize solution is claimed. Prior conservation-law literature is cited in the module. The independent backend agent's conservation question motivated the proof; Troy Lowry and OpenAI Codex supplied the proof and formalization.

Validation at the current reference commit `3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0:

```text
cd lean
lake build Ruliology.CellularAutomata.Rule30LocalConservation
lake env lean --run ../Check.lean Ruliology.CellularAutomata.Rule30LocalConservation --claim partial --headline Ruliology.CellularAutomata.Rule30LocalConservation.cyclic_conserved_iff_shift_coboundary --headline Ruliology.CellularAutomata.Rule30LocalConservation.local_conserved_iff_shift_coboundary --headline Ruliology.CellularAutomata.Rule30LocalConservation.Word.image_eq_four
```

Both pass. The unchanged checker replayed all 195 owned declarations, accepted all three headlines and reported no new axioms. The checker SHA-256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. Its existing replay deprecation warning remains; the new module's build has no warnings.

[Original proof, independent finite controls and scope analysis](https://github.com/Troyusrex2/Rule30PrizeKit/blob/61832c8f56b0aee58d185aa933ca7a3e4365bc4b/research/agent-experiments/coordinator/20261025-greedy-and-conservation/REPORT.md). No new prize essay has been submitted.
