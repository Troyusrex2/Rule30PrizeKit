# Reconstruction identity and limits of its iteration

**No prize problem or eventual period two is excluded here.** This contribution
formalizes an unbounded reconstruction identity, states its exact iteration
condition, and gives two checked counterexamples to stronger extrapolations.

Let `G : Nat → Bool`, and reconstruct leftwards from the white wall and the
boundary history `!G(0),1,!G(1),1,...`. Write
`D G(r) = G(r+2) xor G(r+4)`. A gate is *spaced* when no two black cells have
distance one or two.

The three core-only modules prove:

- **Exact translation.** For a spaced gate, at every depth `m≥1` and every
  time `t`, `recon b_G (m+8) t = recon b_(D G) m t`. An initial support bound
  `W` transfers to `W-8`.
- **Exact preservation condition.** For a spaced gate, `D G` is spaced if and
  only if `G(r+4)=0` for every `r`. Thus an infinite gate loses the condition
  required by this lemma after the first transform.
- **A second translation can be false.** The period-five gate is spaced,
  while its transform is not. Applying the formula twice gives the wrong
  reconstructed cell already at depth 17, time 0: white versus black.
- **The small gap table does not extend with bound sixteen.** The period-31
  gate black at residues `0,3,6,9,12,15,18,21,26` has successive gaps only
  three or five, but its reconstructed initial row is white at every depth
  from 528 through 544. `no_uniform_gap_bound_sixteen` states the failed
  universal bound directly.

`Rule30PackedReconstructionResearch.packed_sound` connects the finite packed
check to the kit's actual scalar `Rule30ZeroBoundary.recon`, with an explicit
light-cone bound. The certificate uses ordinary kernel evaluation. There are
no custom elaborators, external decision procedures or added axioms.

These results do not rule out other renormalizations or a larger gap bound.
No finite driven-right realization of either example is asserted. In
particular, a periodic boundary gate is not a counterexample to Problem 1.

The one-step identity follows the informal identity in
[morpholib Theorem 14](https://github.com/fractastical/morpholib/blob/777865115483d310f72f0b9511b45409e330a8f5/docs/RULE30_PRIZE_SUBMISSION.md).
That source's Theorem 15 reports a small-depth gap table. The examples here
address extrapolating the identity or table beyond its checked conditions;
they do not refute a full prize conjecture. Its linked Lean file contains
local Boolean identities rather than the global period-two elimination
advertised in the prose, which is not used as a premise here.

Credit for the informal one-step identity belongs to the cited morpholib work.
The Lean formalization, support transfer, preservation criterion, finite-cone
engine and counterexamples here were developed by Troy Lowry with OpenAI
Codex. No claim of literature priority is made.

All **73 generated constants** were replayed by the unchanged checker in the
working catalog and the pinned reference kit
`cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554`, with standard axioms only:
[spacing reference check](spacing-pinned-verification.json),
[packed engine and gap reference check](gap-pinned-verification.json).
The reference copies remove only module/export wrappers; proof bodies are
unchanged. The clean contribution's build and replay are recorded in
`catalog-verification.json`. This is independent local verification, not a
new official prize submission or human review.

The independent Wolfram checks compare 12,800 reconstructed cells and
reproduce both counterexamples:
[translation check](wolfram-spacing-probe.json),
[seventeen-cell gap](wolfram-spacing-gap-probe.json).

Reproduce the clean catalog check with Lean 4.35.0 and Python's `psutil`:

```text
python research/renormalization/verify.py --lake /path/to/lake
```

In Wolfram, load `spacing-probe.wl` and evaluate `spacingReport[]`, then load
`spacing-gap-probe.wl` and evaluate `spacingGapReport[]`. The finite experiments
are distinguished from the all-time Lean statements throughout.

## Review essay

The [evaluated notebook](renormalization-essay.nb) embeds the exact
[standalone source](Rule30RenormalizationStandalone.lean).
The unchanged CLI checker and LeanLink each replayed all 73 declarations;
the saved notebook has zero message cells and its source round-trip matches.
See [CLI verification](standalone-verification.json) and
[notebook verification](renormalization-essay.nb.verification.json).

It is prepared for human review and **has not been submitted to the prize
API**. New submission consent is still required. To regenerate the essay,
run `generate_essay.py`, set `RULE30PRIZE_KIT` to a prepared pinned kit, and
evaluate `build-notebook.wl` in a fresh Wolfram kernel with LeanLink installed.
The builder disables conversion caching, inspects the saved notebook and never
submits anything. `IncludeInternal -> True` exposes ordinary theorem names
containing `.rec`, which LeanLink's default display filter otherwise hides;
it does not change the kernel check.
