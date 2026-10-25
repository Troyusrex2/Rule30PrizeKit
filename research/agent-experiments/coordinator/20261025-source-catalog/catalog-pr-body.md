Add a core catalog lemma about the actual seed's black-to-white run-boundary sources. At every scale H=2^e, among depths d<=e and times s<2H-1, exactly one nonzero source passes the explicit even-depth binary support mask: d=0, s=H-1. The proof uses the existing right-diagonal periodicity and finite seed cone, and states the actual-cell source semantics.

This adds the module, its public import and a catalog row. The mask is explicit in the theorem; the separate [kernel-checked Mathlib bridge](https://github.com/Troyusrex2/Rule30PrizeKit/blob/03a01aaa541c5ec1e66c5df63b8c2c330498ea59/research/agent-experiments/coordinator/20261025-source-green/REPORT.md) derives the complete Rule90 source expansion and proves the actual center equals 1 plus the unrestricted deeper-source sum. The core module uses no Mathlib. Neither result controls that deeper sum or solves a prize problem; no novelty is claimed for diagonal periodicity, the local Boolean identity or Lucas' theorem.

Validation at verifier commit 3eca23c0a9fa6b153313655e6d51835406c2d06e:

- `cd lean; lake build Ruliology.CellularAutomata.Rule30RunBoundarySources` passed, including its cold dependencies.
- The unchanged official checker fully replayed all 56 owned constants and accepted `selected_event_iff_outer`, `source_physical` and `rule90_source_identity`, with no new axioms.
- The source build is warning-free. Guarded build and replay completed in 9.313 seconds with about 0.77 GiB peak owned RSS. Exact source, commands, raw reports and independent controls are in the linked research archive.

Contributed by Troy Lowry with OpenAI Codex.
