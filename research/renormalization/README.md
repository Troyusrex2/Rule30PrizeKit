# Empty-right gate spacing and limits of reconstruction iteration

**No prize problem or eventual period two is excluded here.** This contribution
proves an all-time spacing property of the empty-right driven gate, formalizes
an unbounded reconstruction identity, and identifies its exact iteration limit.

Let `u(s)` be position one at physical time `2s+1` of the alternating-driven
right half starting entirely white, as in `Rule30PeriodTwoSideways.u empty`.
For `G(r)=u(146+r)`, Lean proves that black observations have exact successive
spacings **three or five**. No six-cycle gate window is entirely white.

The proof uses a 16-cell forward invariant with 13,937 states. It checks all
262,144 eighteen-bit cases, including every value of the two unseen right
cells, for both closure and the required gate observations. The actual orbit
enters at white cycle 146, physical time 293, with prefix 49415. An induction
then covers every future time. The packed engine is proved equal to the kit's
driven evolution; the program that searched for the invariant is untrusted.

From white cycle 155 (physical time 311, prefix 38682), the actual orbit lies
in a smaller closed wall of 740 states. Every eight-bit gate window is in
`[8,9,16,18,33,36,66,72,132,144]`, encoding the earliest bit in the least
significant position. In particular, a gap of three cannot be followed
immediately by another gap of three. The refinement covers all future times.

This is a property of the actual empty-right driven gate. **It does not prove
`CQ01Empty`: infinitely many black gate observations do not establish infinitely
many black cells in the reconstructed initial left row.** The transformed
actual gate is provably not spaced. It also violates the exact weaker return
condition arbitrarily late, so weakening the spacing premise cannot repair
this particular iteration.

Let `G : Nat → Bool`, and reconstruct leftwards from the white wall and the
boundary history `!G(0),1,!G(1),1,...`. Write
`D G(r) = G(r+2) xor G(r+4)`. A gate is *spaced* when no two black cells have
distance one or two.

The nine core-only modules also prove:

- **Exact translation.** For a spaced gate, at every depth `m≥1` and every
  time `t`, `recon b_G (m+8) t = recon b_(D G) m t`. An initial support bound
  `W` transfers to `W-8`.
- **Exact preservation condition.** For a spaced gate, `D G` is spaced if and
  only if `G(r+4)=0` for every `r`. Thus an infinite gate loses the condition
  required by this lemma after the first transform.
- **Exact return condition.** The full eight-column formula at every depth
  holds if and only if adjacent black gates are forbidden and distance-two
  pairs are forbidden starting at index one. Only the pair at zero and two
  is exempted. For a spaced gate, this weaker condition holds for `D G` if
  and only if `G(r+5)=0` for every `r`. A gate black only at index four shows
  the distinction from preservation of spacing. The actual infinite gate
  violates the transformed condition arbitrarily late, and its universal
  twice-transformed scalar reconstruction formula is false.
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
No finite driven-right realization of either periodic example is asserted. In
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
engines, driven-gate invariant and counterexamples here were developed by Troy Lowry with OpenAI
Codex. No claim of literature priority is made.

All **744 generated constants** were replayed by the unchanged checker in the
working catalog and the pinned reference kit
`cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554`, with standard axioms only:
[spacing reference check](spacing-pinned-verification.json),
[packed engine and gap reference check](gap-pinned-verification.json),
[driven engine, all certificate leaves and infinite induction](driven-wall-pinned-verification.json),
[refined language and all its certificate leaves](empty-language-pinned-verification.json).
The reference copies remove only module/export wrappers; proof bodies are
unchanged. The clean contribution's build and replay are recorded in
`catalog-verification.json`. This is independent local verification, not a
new official prize submission or human review.

The independent Wolfram checks compare 12,800 reconstructed cells and
reproduce both counterexamples:
[translation check](wolfram-spacing-probe.json),
[seventeen-cell gap](wolfram-spacing-gap-probe.json).
An additional [Wolfram check](wolfram-driven-wall-check.json) checks all 55,748
wall transitions, every observation, 256 independent vector-update controls,
and the entry time and prefix. This finite computation supports the certificate;
the unbounded statement is the Lean induction.
The [refined-wall controls](wolfram-empty-core-check.json) independently check
all 2,960 smaller-wall transitions, the ten allowed words, 256 vector controls,
and first entry at cycle 155.

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
The unchanged CLI checker and LeanLink each replayed all 744 declarations;
the saved notebook has zero message cells and its source round-trip matches.
See [CLI verification](standalone-verification.json) and
[notebook verification](renormalization-essay.nb.verification.json).
The [reading export](renormalization-essay-evaluated.md) was inspected through
the notebook reader; that display abbreviates large cells, while the notebook
and standalone file retain the complete exact source.

It is prepared for human review and **has not been submitted to the prize
API**. New submission consent is still required. To regenerate the essay,
run `generate_essay.py`, set `RULE30PRIZE_KIT` to a prepared pinned kit, and
evaluate `build-notebook.wl` in a fresh Wolfram kernel with LeanLink installed.
The builder disables conversion caching, inspects the saved notebook and never
submits anything. `IncludeInternal -> True` exposes ordinary theorem names
containing `.rec`, which LeanLink's default display filter otherwise hides;
it does not change the kernel check.

`generate_driven_wall.py` reproduces the untrusted wall search with NumPy and
emits the same checked source. Ordinary catalog builds and kernel replay do not
depend on Python, NumPy or the generator. `verify_standalone.py --project
/path/to/pinned-kit --lake /path/to/lake` checks the exact essay source without
generating native C artifacts.
`generate_empty_core.py` reproduces the smaller-wall search using NumPy and
SciPy. It imports `empty_gate_controller.py`; these discovery programs are
likewise outside the trusted proof path.
