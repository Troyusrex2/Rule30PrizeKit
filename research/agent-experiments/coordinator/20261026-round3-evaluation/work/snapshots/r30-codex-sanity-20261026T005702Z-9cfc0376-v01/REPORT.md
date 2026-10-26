# Periodic-tail surgery: does a fake repeating future require an infinite seed repair?

Response: `r30-codex-sanity-20261026T005702Z-9cfc0376-v01`  
Agent: codex-sanity / Codex. Track E. One finding, **F001 — EXPERIMENT**.  
Independent response; supersedes none. Prepared for Troy's local coordinator inbox.

The off-the-wall idea is to deliberately counterfeit Rule 30's future: replace its center column with a repeating tail, then reconstruct the seed that would make that forged history true. Think of checking a coin's provenance backward: each apparent repair may demand another alteration farther back. Can Rule 30's nonlinear OR term force these seed repairs to regenerate at every doubling of distance?

The inverse construction is already known. The proposed target is an **unproved regeneration lemma**, with a small exact experiment to make it falsifiable. No unbounded argument emerged, and this is not a solution or a new period exclusion.

## Exact target and bridge to Problem 1

Use physical cells `x_p(t)` with

```text
x_p(t+1) = x_(p-1)(t) XOR (x_p(t) OR x_(p+1)(t)).
```

Let `c(t)` be the official center column from the single black cell at the origin. For integers `T >= 0`, `P >= 1`, define a prescribed trace using the actual seed's next P bits:

```text
u_(T,P)(t) = c(t)                         when t < T,
             c(T + ((t-T) mod P))         when t >= T.
```

Keep initial positions `p >= 1` white. Let `b_(T,P)(m)` be the initial cell at position `-m` in the unique row realizing this prescribed trace. Here `b(0)=1`, so every black `b(m)` with `m>0` is an extra seed edit. This preserves the actual seed's trace through time `T+P-1`; it does not assume a later disagreement.

**Open regeneration conjecture:** for every `T,P`, there exists an integer `M >= 1` such that every `k >= 0` has some `m` satisfying

```text
M*2^k <= m < M*2^(k+1)    and    b_(T,P)(m)=1.
```

This is a stronger sufficient target, not a claimed equivalence. If the actual `c` were periodic after `T` with period `P`, then `u_(T,P)=c` at every time. Uniqueness would force `b=(1,0,0,...)`, contradicting regeneration. Thus a proof for all `T,P` would prove official Problem 1. Merely asking that `b` differ from the seed is the catalog's existing reformulation; that alone is no advance.

## Mechanism worth trying

First evolve the initially white right half under the prescribed boundary `u`, obtaining the adjacent column `R(t)=x_1(t)`. With `C_0=u` and `C_1=R`, reconstruct leftward by the exact identity

```text
C_(j-1)(t) = C_j(t+1) XOR (C_j(t) OR C_(j+1)(t)),   j <= 0.
b(m) = C_(-m)(0).
```

Search for a scale-to-scale certificate in these reconstruction triangles: an OR saturation pattern that forces a black initial cell in the next distance interval, despite XOR cancellation. It must retain enough boundary-column information to justify the transition. Counting black cells or recording only the period word cannot establish this certificate; periodic forcing does not make the driven right half bounded or periodic.

The concrete first probe fixes `M=2*(T+P+1)`. That particular bound is optional and stronger than the existential conjecture. A zero annulus would refute the fixed-M proposal at that pair, not necessarily every larger choice of M. No closed transition system or regeneration invariant has been proved here.

## Exact finite result

The attached Python program reconstructed 2,048 initial cells for every `T=0..16`, `P=1..16`: **272 cases**. Every one of the **1,514 complete doubling intervals** with the fixed M contained an extra black seed cell. Each reconstructed prefix had 292 to 1,380 extra black cells. These are measurements over this grid, not density estimates or proof of infinite support; some pairs prescribe the same trace and are not independent evidence.

Controls passed:

- All 128 seven-bit traces for each of Rules 30, 90, 150 and 210 were inverted and replayed using a separate physical-coordinate truth-table simulator: 512 cases.
- All 272 surgery seeds replayed exactly to their prescribed 2,048-bit traces. Reconstruction agreed at prefix lengths 31, 64, 128 and 512, giving 1,088 consistency checks. The actual unmodified trace inverted to seed 1.
- The first extra seed bit matched the first altered trace bit. This checks the known triangular sensitivity; it is not a growth argument.
- Rules 90, 150 and 210, with their own actual seed traces and `T=1,P=1`, required **zero** extra seed edits. Generic left-permutivity therefore cannot supply the proposed Rule 30 mechanism.

**A stronger shortcut failed:** demanding an edit in every P-cell interval starting at or beyond `T+P` fails already at `T=0,P=1`: `b(1)=0`. The prescribed trace is constant one; its tested inverse begins `101010...`, read from the origin leftward. This failure is retained as a limitation of the same experiment.

## Prior work, scope and reproduction

At research commit `102d5b8e938b031a6d4df53541d9da2c50ffb859`, catalog [22] and `Rule30Realization.lean` already provide `lc`, `realize`, `column_realizable_unique`, `unique`, and `evol_seed`. The catalog also states the 2-adic isometry interpretation. These are credited interfaces, not new findings. Source URLs and exact blob hashes are in `evidence/referenced-sources.json`.

The same module's `seed_perturbation` is the essential warning: a row can match the seed on any prescribed finite region while producing an eventually white center. Finite prefixes cannot settle the question. The kit's period-two decoder has a related open finite-support obstruction; this proposal fixes the initial right half white and uses actual-prefix surgeries across all periods. It does not solve that unrestricted period-two problem. The response-growth counterexample also prevents assuming bounded state from a periodic driver.

The refreshed public index contained 40 entries and reported update time `2026-10-26T00:57:03Z`. Related entry `R30-20261023-7e9e6e` credits Quint and Gemini for left-cone reconstruction and the four-rule comparison. Its public abstract was checked for overlap; its source was not independently replayed here or used as a new proof premise. No exhaustive novelty claim is made. This experiment does not depend on or supersede either earlier codex-sanity response.

Run from this response directory, with a new output directory:

```text
python src/run_guarded.py --output reproduce-output
```

Environment: Python 3.12.3, psutil 5.9.8; exact integer/Boolean arithmetic, no solver or GPU. The guarded run completed in 1.906 seconds, with 22,245,376 bytes peak sampled child RSS. Limits: 300 seconds, 8 GiB owned process-tree RSS, at least 2 GiB available memory. No Lean build or kernel replay was performed. Source, every reconstructed prefix, the original trace, raw log and run metadata are attached and hashed in the manifest.

**Smallest useful next step:** try to falsify the fixed-M annulus rule on held-out larger onsets and periods, then inspect the least populated surviving triangles for a reusable OR/cancellation certificate. Formalize only a transition that covers all realizable boundary states. A broad parameter sweep without that transition is more finite evidence, not the missing proof.
