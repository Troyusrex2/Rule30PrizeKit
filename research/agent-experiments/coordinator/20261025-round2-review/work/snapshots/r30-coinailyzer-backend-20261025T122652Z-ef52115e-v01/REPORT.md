# R2-01: Readers that keep or resynchronize to the background escape the two-step barrier but fail the full rank requirement at unit scale

Response ID: r30-coinailyzer-backend-20261025T122652Z-ef52115e-v01
Agent: CoinAIlyzer Backend Bot (claude-opus-5-5, Claude Code). Task: **R2-01**.
Original response: r30-coinailyzer-backend-20261024T214457Z-6932e764-v01 (the mint-mark reader, which was refuted). Supersedes: none.
Research base: 102d5b8e938b031a6d4df53541d9da2c50ffb859.
Verifier pin: 3eca23c0a9fa6b153313655e6d51835406c2d06e, Lean 4.35.0. **No Lean was written or run in this response; nothing here is kernel-checked.**

## Batch overview

All three findings concern signed prefix energies of the barrier's form,
`E_r(w) = H_r + sum_i lambda^i C_r(state before w[i], w[i])`. F002 and F003
cover the unit scale `lambda = 1` only. None of the findings proves CQ01, Q01 or Problem 1.

- **F001 (EXPERIMENT, exact).** Two kinds of simple reader satisfy all three of the barrier's conditions
  (the lower bound, the strict drop A→M and the non-increase M→Z), using nonnegative 0/1 costs:
  - an 8-state prefix-match reader, at every integer `lambda >= 1`;
  - sliding-window readers, for `L >= 5` at `lambda = 1` and for `L >= 8` at every tested `lambda`.

  So the barrier's witness words cannot be reused against readers that keep or resynchronize to the background.
  Any extension must use more of the rank requirement.
- **F002 (EXPERIMENT: paper reduction plus exact rank certificate).**
  Consider a definite (resynchronizing) reader at unit scale. The full requirement on guarded rows forces its cost
  density to be a conservation law of four Rule 30 steps. An exact computation shows that Rule 30^4 has only trivial
  conservation laws for window length `m <= 11`. With only trivial laws, the energy is `c*length + O(1)` with `c >= 0`,
  and a long truncated ether orbit contradicts the required drops.
  So no unit-scale definite reader with delay `L <= 10` works. The missing lemma is the same statement for every `m`.
- **F003 (EXPERIMENT: paper reduction plus exact finite checks).**
  Consider any reader with a sink state that it reaches on the stated pump rows and on every `Theta(g)` prefix
  for factors `g` of one aperiodic Golden stream. The round-two **1,110-state union reader** is one such reader,
  and it keeps the period-seven background. For such readers, no unit-scale two-phase signed rank exists on the
  Golden-guarded domain. An exact Farkas certificate forces all four sink costs to be equal; a Fibonacci-stream
  orbit then gives the contradiction.
  This is consistent with the archived unit-scale `alpha = 0` optima. Those runs used richer models
  (finite history and upcoming-bit phases), which this argument does not cover as written.

Route to Problem 1: none of this supplies a rank. It narrows where one could
exist:
- A unit-scale local energy would have to be a nontrivial Rule 30^4 conservation law that drains through the wall
  (F002). None exists for `m <= 11`.
- A unit-scale reader that absorbs once the input leaves finitely many backgrounds is ruled out (F003).

Still open:
- non-unit scales for F002 and F003;
- readers that are neither definite nor absorb off the backgrounds (unbounded counters, stack memory);
- costs that depend on the right half;
- different lower-bound domains.

Conventions (the kit's ZBL convention):
- Word index `i` is depth `i+1`, and the wall is at depth 0.
- The update is `new(k) = old(k+1) XOR (old(k) OR old(k-1))`.
- `next` is the kit's two-update `Rule30FiniteLeftWordResearch.next` (length +2, no truncation).
- The phase `r` of a row is its previous free bit, as in the barrier (`E_1` on A and Z, `E_0` on M).
- A free-zero step must drop by at least 1, and a free-one step must not increase.
- The "guard" means black even-time heads plus the stated odd-time stream for the next 13 double steps, as in `Safe13`.
  The 0101 stream is the barrier's; "Golden" means the stream has no `00` and no `11111`.

## F001: The barrier's two-step witnesses are satisfied by retaining and resynchronizing readers

- **Track/status:** G, EXPERIMENT. This is an exact finite computation with no Lean.
- **Exact claim.** Let `A, M, Z` be the barrier's `startWord`, `middleWord` and `endWord`, of lengths 34, 36 and 38.
  Here `A = w0 ++ 1011`, where `w0` is the first 30 cells of `(1100001)^inf`.
  The backgrounds are `(1100001)^inf` for A and Z, and `(1011111)^inf` for M.
  - (a) Prefix reader `P`: 7 phase states plus a reject sink. A letter that matches the background costs 1; otherwise the cost is 0.
    The matched lengths are A 30, M 28 and Z 26. Z's matched positions are a strict subset of A's.
    So for every integer `lambda >= 1`, `E1(Z) < E1(A)`. Taking `H1 = 0` and `H0 = E1(Z) - E0(M)` satisfies conditions 2 and 3.
    Condition 1 holds on every word with `B = 0`, because all costs are at least 0.
    `P` is not absorbed anywhere on `commonWord = A[:26]`, so the barrier's hypothesis fails for it.
  - (b) Window reader `W_L`: a letter costs 1 when the last `L+1` letters (padded with white at the wall) form a factor of the background.
    It never absorbs, because it is definite. The conditions hold at `lambda = 1` for `L = 5..15`.
    For `L = 8..15` they hold at every `lambda >= 1`, because the matched positions are a strict subset.
- **Barrier check.** `P` falls outside the barrier because it keeps the background, and `W_L` because it resynchronizes.
  Neither is a counterexample to the barrier, and neither is a rank.
- **Falsification run.** `python src/f001_barrier_escape.py`, written to `evidence/f001-barrier-escape.json`. It uses integer arithmetic only.
- **Result.** The exact computation proves the statement, which concerns three explicit words.
- **Missing lemma / next action.** An extension must use more steps of the dynamics; F002 and F003 do this.
  A Lean `decide` check of (a) against the barrier's own definitions would be cheap. It was not done.
- **Limitations.** Only the three barrier conditions were tested.

## F002: Unit-scale definite readers reduce to Rule 30^4 conservation laws, and none exist for window m <= 11

- **Track/status:** E, EXPERIMENT. The reduction is a paper argument; the rank computation is exact.
- **Modeled proposition.** The method lies outside the barrier because the reader never absorbs.
  - A definite reader with delay `L` has energy `E_r(w) = H_r + sum_{i<|w|} phi_r(w[i-L..i])`.
    The window is padded with white at the wall, `lambda = 1`, and `phi_r` is signed and rational.
  - Step requirement (S): for every guarded row `w` of phase `r` with an actual finite predecessor,
    `E_b(next w) <= E_r(w) - [b = 0]`, where `b` is the next free bit.
  - Lower bound (LB): `E_1` is bounded below.
  - The rows used are an ether-phase prefix followed by an arbitrary tail, plus long truncated ethers.
    All of them lie inside the barrier's own 0101 and 1010 `Safe13` domains.
- **Reduction (paper proof, not formalized).**
  1. Fix a 40-cell ether-phase prefix. Every finite middle word appears in some guarded image row, with only a bounded junk region:
     back-solve the predecessor (each double step is permutive in the deepest cell), then pad with white.
     - The change in energy is a Birkhoff sum of `h_rb = phi_b o F - phi_r` over the middle, plus bounded boundary terms.
       Here `F` is the bulk double step.
     - Periodic middles `Y^n` can be realized for every periodic `Y`, because surjective CA have periodic preimages of periodic points.
     - So the sum of `h_rb` around every de Bruijn cycle is at most 0.
  2. `F` is balanced: each `(L+1)`-word has 16 preimages of length `L+5`.
     - Therefore `mean(h_10) + mean(h_01) = 0` under the uniform measure. Each mean is at most 0, so both are 0.
     - Longest-path potentials and the uniform circulation then force both functions to be exact coboundaries.
     - Hence `phi_1 o F^2 - phi_1` is a coboundary. That is, `phi_1` is a conserved density of `F^2`, which is four Rule 30 steps.
       Also `phi_0` is cohomologous to `phi_1 o F`.
  3. If every conserved density is trivial, then `phi_r = c + coboundary` and `E_r(w) = H_r + c|w| + O(1)`.
     - The all-white pump in the barrier's domain gives `c >= 0`.
     - A truncated ether of width `l` stays guarded for about `(l-27)/2` double steps
       (`evidence/f002-ether-lifetime.json`: 109 double steps with 55 free zeros at `l = 240`).
     - Along that orbit the energy must fall by the number of free zeros. Instead it changes by `+2c` per step plus `O(1)`.
       This is a contradiction for large `l`.
- **Falsification actually run.** `src/f002_conservation.py`.
  - For window `m`, the script builds the integer system `Phi(G e) = Phi(e)` over every word `e` of length `m+2k`.
    These are the fundamental de Bruijn cycles through `0^(n-1)`, with `phi(0^m) = 0`.
  - The trivial solutions span a space of dimension `2^(m-1) - 1`, so the rank is at most `2^(m-1)`.
  - The script computes the GF(p) rank (`p = 2^31-1`) of a subset of the rows. That rank is a lower bound on the rational rank.
    If it equals `2^(m-1)`, this certifies exactly that only trivial laws exist. A shortfall would only be inconclusive.
  - Rule 30 with `k = 1, 2, 4` steps and `m = 1..10`: all 30 cases certified trivial (1 min 52 s in total).
  - Rule 30 with `k = 4` and `m = 11`: certified trivial (12,160 equations, 2,047 unknowns, rank 1,024, 297 s).
  - Positive control, Rule 184 (which conserves the number of ones), with `k = 1, 2, 4` and `m = 1..5`:
    the rank falls short by exactly 1 every time, as expected.
- **Result.** The computation shows that Rule 30^4 has no nontrivial conserved density of window `m <= 11`.
  Because laws conserved by Rule 30 or Rule 30^2 are also conserved by Rule 30^4, this covers Rule 30 and Rule 30^2 as well.
  Together with the reduction, no unit-scale definite reader with `L <= 10` satisfies (S) and (LB).
  Not proved: the three reduction steps in Lean, and the case `m > 11`.
- **Positive reading (the missing physical bridge).** A unit-scale local resource for this method must be a
  conservation law of four Rule 30 steps that has a nonnegative representative and whose flux through the white wall
  is negative at every guarded free-zero step. For `m <= 11` no such law exists.
  Otherwise a local reader needs a non-unit scale or nonlocal memory.
- **Missing lemma.** For every `m` and every `phi : {0,1}^m -> Q`: if `phi o R30^4 - phi` is a coboundary,
  then `phi` is a constant plus a coboundary. We know of no proof that covers every `m`, and we did not search the literature thoroughly.
- **Limitations.**
  - `lambda = 1` only, because geometric weights do not telescope.
  - Definite readers only, not general synchronizing automata.
  - (S) is the full requirement on the stated rows, which is stronger than the barrier's two steps.

## F003: Readers that absorb only off finitely many backgrounds admit no unit-scale rank on the Golden-guarded domain

This class includes the round-two 1,110-state union reader.

- **Track/status:** H, EXPERIMENT. The reduction is a paper argument; the finite ingredients are exact computations.
- **Modeled proposition.**
  - The same `T` serves both phases, with signed integer costs `C_0, C_1`, offsets `H_0, H_1`, and `lambda = 1`.
  - (S) holds on every row with a black head, an actual finite predecessor whose step had free bit `r`,
    and a 13-double-step guard whose stream is Golden. (LB) is as in the barrier.
  - Hypotheses on `T`: there is a sink `s` such that
    - (P) the reader is absorbed on the pump rows below and their successors, and
    - (X) the reader is absorbed within `p0` cells on `Theta(g)[1..78]` for every length-40 factor `g` of `f`.
- **Why it is outside the barrier.** The 1,110-state reader is not absorbed on `commonWord`:
  it tracks all 14 phases of the free-period 01/011/0111/01111 backgrounds.
  The obstruction uses different rows: pump rows separated by a white run, and an aperiodic Golden orbit.
- **Argument (paper).**
  1. Pump rows are `R_n = next(P_n)` with `P_n = Q ++ 0^30 ++ Y'^n ++ 1`.
     `Q` is a 40-cell ether-phase prefix (phase 1 or 0), `Y` is one of `0`, `1`, `10000000`, and `Y'` is a periodic preimage of `Y`.
     - The reader is in the sink by cell 40 in both `R_n` and `S_n = next R_n`, so the energies are affine in `n`.
       (S) for all `n` forces the slope to be at most 0.
     - Write `c = C_1(s,.)` and `d = C_0(s,.)`. The six slope inequalities are:
       - `d0 <= c0`, `c0 <= d0`
       - `3d0 <= 3c1`, `3c0 <= 3d1`
       - `5d0 + 3d1 <= 7c0 + c1`, `5c0 + 3c1 <= 7d0 + d1`
     - An exact nonnegative certificate (checked with Fractions in the evidence file) derives `c0 = c1 = d0 = d1 =: a`.
       The white pump together with (LB) gives `a >= 0`.
  2. Let `f` be the Fibonacci word over the blocks `01` and `011`. It is Golden and aperiodic.
     Let `w` be the canonical truncation of `Theta(f)` at width `W`, and `w_j = next^j w`.
     - For `j <= (W-78)/2`, `w_j[1..78] = Theta(sigma^j f)[1..78]`, by the kit's `two_step_shift` and light-cone locality.
       This prefix depends only on a length-40 factor of `f`.
     - By (X), the reader is in the sink by cell 16. So `E_{r_j}(w_j) = H_{r_j} + score_{r_j}(w_j[1..16]) + a(|w_j|-16)`, with `|w_j| = |w| + 2j`.
     - Summing (S) over the orbit gives `2a*j - K <= -#zeros(f[1..j])`. Here `K` is bounded, because there are finitely many 16-cell prefixes and two phases.
     - The number of zeros grows without bound, so this is a contradiction.
- **Falsification actually run.**
  - `src/export_t1110.py` rebuilds `T` from the coordinator's unmodified source, run from a scratch copy whose hashes are in `evidence/upstream-sources.json`.
    Its own controls report `all_passed`, with 1,110 states and 14 patterns.
  - `src/f003_background_reader.py` then checks three things.
    - (P): all three `Y` families, both phases, `n = 1..40`.
      - The guard holds for both `R_n` and `S_n`.
      - The sink is reached at cell 39 or 40 in `R_n` and at cell 37 or 38 in `S_n`.
      - The tally slopes exactly equal the per-period tallies of `Y` and `next Y`.
      - The six-part exact certificate holds.
    - (O): `W = 801` over 360 double steps.
      - The guard holds with stream `sigma^j f`.
      - The 60-cell prefix equals `Theta(sigma^j f)`.
      - The sink is reached by cell 16.
      - There are 151 free-zero steps.
    - (X): all 41 bit-factors of length 40 drive the reader to the sink within 16 cells.
      - The list is complete: the Fibonacci word has `n+1` factors of length `n`, and all 31 block factors of length 30 are present.
      - The longest white run in any background is 7.
- **Result.** Every finite hypothesis instance listed above was computed.
  The paper proof then shows that no unit-scale two-phase rank exists for this reader on the Golden-guarded domain.
  It assumes (P) for all `n`: this was checked for `n <= 40`, and locality gives all `n` but is not formalized.
  The argument uses no property of the reader's size or transition table beyond (P) and (X).
- **Missing lemma / next action.**
  - Formalize a generic Lean theorem over `T` with hypotheses (P) and (X), next to `no_absorbing_prefix_geometric_rank`.
    The pieces are the pump families for all `n`, Theta-orbit locality, and the decidable factor check.
  - Then extend step 1 to the 5-context (`4 - r` reward) and upcoming-phase models used in round two.
    Step 1 should extend because the context graph is strongly connected, but this was not checked.
- **Limitations.**
  - `lambda = 1` only. With `lambda > 1` the slopes are geometric, and step 1 does not apply as stated.
  - Two-phase model only.
  - The step domain is the Golden-guarded domain, which is wider than the barrier's 0101 lower-bound domain.
    A rank that proves Q01 for an unknown Golden stream needs this wider domain.
  - Not covered: readers that resynchronize to a background after a mismatch without being definite, and readers with unbounded memory.

## Reproduction and delivery

Environment: Windows 11, Python 3.12.3 and NumPy 1.26.4. No SciPy, no LP and no solver were used.
Every verdict is exact integer, Fraction or GF(p) arithmetic. Commands, run from `src/`:

```
python f001_barrier_escape.py > ../evidence/f001-barrier-escape.json
python f002_conservation.py 1,2,4 10 ../evidence/f002-conservation-rule30.json 30
python f002_conservation.py 4 11 ../evidence/f002-conservation-rule30-k4-m11.json 30 11
python f002_conservation.py 1,2,4 5 ../evidence/f002-conservation-rule184-control.json 184
python ether_lifetime.py > ../evidence/f002-ether-lifetime.json
python export_t1110.py <scratch copy of round2 evidence/left-future-history-multi> ../evidence/t1110
python f003_background_reader.py ../evidence/t1110/T1110.npy ../evidence/t1110/pats.json > ../evidence/f003-background-reader.json
```

Resource bounds: each run had a 15-minute `timeout`, the longest took 5 minutes, and peak memory stayed below about 1 GB.
No check failed. The GF(p) rank method can be inconclusive, but it was never inconclusive for Rule 30.
No credentials or machine configuration are included.
