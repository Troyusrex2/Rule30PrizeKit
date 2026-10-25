# R2-02 (photograde): coupled readers find no seed signature; one exact reduction to column-1 inheritance

- Response ID: r30-photograde-20261025T122841Z-abce3ea0-v01
- Task: R2-02
- Original response: r30-photograde-20261024T214729Z-bffceeb4-v01
- Research base: 102d5b8e938b031a6d4df53541d9da2c50ffb859
- Verifier pin: 3eca23c0a9fa6b153313655e6d51835406c2d06e, Lean 4.35.0. **No Lean was run.**

## Batch overview

The round-one idea was a trace-only class reader, and it collapsed under the coordinator's controls. This round uses only **coupled** data: two-sided multi-column windows and the actual neighbor column. Every experiment uses these controls:

- Rule 150 as the positive control and Rule 90 as a sanity control.
- A shuffled-label run for every model.
- Holdout by whole time ranges.
- Disjoint random orbits for training and testing.

Findings:

- **F001 (FAILED):** coupled windows carry no detectable seed signature in Rule 30. Rule 150's seed is detected at 99.6–99.9%.
- **F002 (FAILED):** the actual seed's column 1 is no more predictable from columns 0 and 1 than a generic orbit's column 1.
- **F003 (EXPERIMENT, paper proof only):** an exact reduction. Columns 0 and 1 can never be jointly eventually periodic, so Problem 1 follows from one missing lemma: "eventually periodic column 0 implies eventually periodic column 1". This is probably already known. It is included to pin the missing lemma down precisely.

**Conventions:**

- Physical frame `cell(t,x)`, seed `cell(0,0)=1`.
- Rule 30: `new(x) = cell(x-1) XOR (cell(x) OR cell(x+1))`.
- The simulated strip is wide enough that no boundary effect reaches |x| ≤ 64 within 4096 steps.

## F001: two-sided coupled windows do not distinguish the seed orbit (FAILED)

- **Track/status:** E, FAILED.
- **Question:** can a classifier tell windows from the actual single-seed orbit apart from windows from orbits of random finite rows? Each window covers 5 columns (x=-2..2) × 8 time steps. The random rows are 33-cell random blocks evolved under the same rule.
- **Holdout:**
  - Seed windows: train on t in [64,1024), test on t in [1024,4088).
  - Negatives: 20 random orbits for training and 20 *different* random orbits for testing, at the same time ranges.
  - 2000+2000 rows per split.
  - Models: logistic regression and gradient-boosted trees, each with a shuffled-label control.
- **Result (held-out accuracy):**

| rule | logistic | boosted | shuffled (log / boost) |
|---|---|---|---|
| 30 | 0.499 | 0.492 | 0.491 / 0.487 |
| 150 (positive control) | 0.996 | 0.999 | 0.576 / 0.404 |
| 90 | 0.506 | 0.506 | 0.496 / 0.502 |

  Rule 90 is degenerate as a control. Near the center, both its seed orbit and its random orbits are almost all white (densities 0.0005 and 0.006). Rule 150 is therefore the meaningful positive control. It shares Rule 30's locality, and the pipeline does find its seed structure. The same pipeline finds none for Rule 30.
- **Barrier check:** this is not an additive prefix score, so the absorbing-prefix barrier does not apply. It is a finite statistical test and proves nothing unbounded.
- **Limitations:**
  - One window shape, two model families, finite times.
  - The negatives are generic random rows, not adversarial matched twins.
  - The result says only that the seed's local coupled statistics look generic, not that no seed-specific invariant exists.
- **Next action:** none on this line. Further local-window learning for Rule 30 is not worth the budget.

## F002: the driven column is not more predictable for the seed (FAILED)

- **Track/status:** D, FAILED.
- **Question:** under coupling, column 1 is driven by column 0: `c1(t+1) = c0(t) XOR (c1(t) OR c2(t))`. Does the seed's column 1 carry *extra* predictability from columns 0 and 1, beyond what a generic orbit has? Such extra predictability would hint at a seed-specific inheritance mechanism (see F003).
- **Features and leakage control:** the features are `c0[t-11..t+1]` and `c1[t-11..t]`. `c0(t+2)` is **excluded**, because it depends on `c1(t+1)`, the target.
- **Holdout:** train on t in [76,2048), test on t in [2048,4094). The generic baseline uses disjoint random orbits, subsampled to the same training size (1972).
- **Result (held-out accuracy predicting `c1(t+1)`):**

| rule / source | logistic | boosted | shuffled boosted | majority class |
|---|---|---|---|---|
| 30 seed | 0.744 | 0.876 | 0.492 | 0.502 |
| 30 random orbits | 0.741 | 0.895 | 0.489 | — |
| 150 seed | 0.917 | 0.959 | 0.625 | 0.667 |
| 150 random orbits | 0.524 | 0.514 | 0.489 | — |
| 90 seed | 1.000 | 1.000 | 1.000 | 1.000 (degenerate) |

  Rule 30 accuracy above the naive 0.75 comes from generic local inference of the unseen `c2` from past bits. It appears equally in random orbits (0.895 vs 0.876), so there is **no seed-specific excess**. Rule 150's seed structure is detected again.
- **Limitations:**
  - One RNG seed and no error bars. The 0.02 gap is within plausible run-to-run variation, and it points away from a seed effect.
  - Finite windows; this does not rule out nonlocal or long-range inheritance.
- **Next action:** stop. Inheritance, if it holds, is not visible as local statistical coupling.

## F003: columns 0 and 1 cannot be jointly eventually periodic, so Problem 1 reduces to column-1 inheritance (EXPERIMENT)

- **Track/status:** D, EXPERIMENT. Paper proof only, **not kernel checked**. Likely already known.
- **Claim:** for Rule 30 from the single seed, there are no T ≥ 0 and P > 0 with `cell(t+P,0) = cell(t,0)` and `cell(t+P,1) = cell(t,1)` for all t ≥ T. The same argument rules this out for any adjacent pair of columns (x, x+1).
- **Proof:**
  1. Rule 30 is left-permutive: `cell(t,x-1) = cell(t+1,x) XOR (cell(t,x) OR cell(t,x+1))`.
  2. If columns x and x+1 are P-periodic from T, the right-hand side is P-periodic in t for t ≥ T. So column x-1 is P-periodic from T, and by induction so is every column ≤ x.
  3. Take k = |x| + T + P. The light cone gives `cell(t,-k) = 0` for t < k. Column -k is therefore white on [T, T+P) ⊆ [T, k). That is a full period, so column -k is white for all t ≥ T.
  4. But the left edge is always black: `cell(k,-k) = 1`, with k ≥ T. Contradiction. ∎
- **Consequence:**
  - Suppose column 0 is eventually periodic (T₀, P₀) and column 1 is eventually periodic (T₁, P₁). Then T = max(T₀,T₁) and P = lcm(P₀,P₁) contradict the claim.
  - So **Problem 1 follows from the missing lemma "if column 0 is eventually periodic, then column 1 is eventually periodic"**. This is the fixed-column inheritance that swarm's run 214719Z did not establish.
  - The reduction is only a reformulation, not an advance in itself. Its value is that it isolates the needed step as a statement about a driven system: `c1(t+1) = c0(t) XOR (c1(t) OR c2(t))`, with `c0` periodic and the finite right half fixed by the seed.
- **Evidence:**
  - The left-permutive identity was checked exactly on the actual seed for 126 columns × 600 steps, with 0 mismatches (A003).
  - The light-cone and left-edge facts are standard.
- **Next action:**
  1. Formalize the claim in Lean against the official definitions. It is short and needs no search.
  2. Attack inheritance through track D's driven right half, starting from the inverse-OR domain: where `c1(t)=0`, `c2(t)` is recoverable as `c1(t+1) XOR c0(t)`.
- **Limitations:** the reduction is probably known to the coordinator. The inheritance lemma may be as hard as Problem 1 itself.

## Reproduction and delivery

- **Command:** `python -I src/coupled_experiments.py F001|F002|F003`
- **Environment:** Python 3.11, numpy 1.24.3, scikit-learn 1.4.2. Set `LOKY_MAX_CPU_COUNT=4` to silence a harmless joblib warning (`logs/` shows it).
- **Determinism:** RNG seed 20261025.
- **Runtime:** about 20 seconds per run on a desktop CPU.
- **Dependencies:** none custom. No credentials and no Lean code.
- **Rerun history:** F002 was re-run once after the first run gave the generic baseline about 10 times more training data than the seed. A004 holds the matched rerun only.
