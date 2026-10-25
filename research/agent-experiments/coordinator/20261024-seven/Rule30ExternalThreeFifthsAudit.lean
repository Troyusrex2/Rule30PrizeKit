import Rule30PrizeKit
import Ruliology.CellularAutomata.Rule30CenterRuns
import Ruliology.CellularAutomata.Rule30BlackRuns

/-!
# Rule 30 Prize submission: black runs of the center column are at most three fifths of their
starting time

This file holds the same definitions and proofs as the module
`Ruliology.CellularAutomata.Rule30CenterRunsFifths` proposed for the kit, in
`namespace Rule30Submission`, so that it checks against a kit that does not have that module yet.

**Partial result.** For the center column `c t = Rule30Prize.center t` of rule 30 from a single
black cell, a run of length `L` starting at time `a` is stated as in `Rule30CenterRuns`:
`∀ i, i < L → center (a + i) = b` (not necessarily maximal).

* **Black runs** (`black_run_three_fifths`). A black run that starts at time `a ≥ 1` has length
  `L ≤ a - 2 ⌊(a - 1) / 5⌋`, hence `5 L ≤ 3 a + 10` (`black_run_five_le`). This replaces the
  bound `L ≤ a` of `Rule30CenterRuns.black_run_le` by a bound with slope `3/5`.
* **Alternating blocks anywhere in the light cone** (`alt_block`). If at time `t` the row
  reads an alternating word of either phase (`Alternating`) on the cells `-m, …, -r` with `m ≤ t`, then
  `5 m ≤ 3 t + 2 r + 6`. In diagonal coordinates `d = t - k`, a block whose right end is on
  diagonal `d₂` starts on a diagonal `d₁ ≥ (2 d₂ - 6) / 5`.
* **Any column, any configuration with a leftmost black cell** (`black_run_evol`). With
  `e = a + i - lo` the time since the left edge passed column `i`: for every `s < a` with
  `5 s + 1 ≤ e`, a black run of column `i` starting at time `a` has length `L ≤ e - 2 s`. This
  sharpens `Rule30CenterRuns.black_run_le_evol` (`L ≤ a + i - lo`).
* **White runs, relative to the right front** (`white_run_front`). If at the start `a ≥ 1` of a
  white run the first black cell right of the center is at column `ℓ + 1`, then
  `L ≤ a - 2 ⌊(a - ℓ - 3) / 5⌋`, so `5 L ≤ 3 a + 2 ℓ + 14` (`white_run_five_le`). Such an `ℓ`
  always exists (`white_run_exists_front`).
* **White runs after nine black cells** (`white_run_after_nine_black`). If the nine cells
  `c (a - 9), …, c (a - 1)` are black, `Rule30BlackRuns.nine_black` puts the first black cell right
  of the center at column `2` at time `a`, so a white run from `a` has `5 L ≤ 3 a + 16`. This is
  the only bound on white runs here that does not depend on `ℓ`.
* **White cells.** Every window `[a, (8 a + 10) / 5]`, `a ≥ 1`, holds a white cell
  (`exists_white_three_fifths`). Hence, before time `n`, at least `m` white cells whenever
  `19 · 8^m ≤ 5^m · (3 n + 16)` (`whiteCount_eight_fifths`), that is about `log_{8/5} n` white
  cells, and `log₂ n ≤ whiteCount n + 1` (`log_two_le_whiteCount`), which is the better of the two
  for small `n`. `Rule30CenterRuns.log_le_whiteCount` had `⌊log₄ n⌋ ≤ whiteCount n`.

**The argument.**

*The block heals backward.* Under a black run, `Rule30CenterRuns.black_triangle` makes the row at
time `a` alternate (`cell a (-k) = [k even]`) for `k < L`. Going back in time, left-permutivity
(`Rule30Jen.cell_left`, packaged as `LeftPerm`) computes the row at time `t` from the row at time
`t + 1` and two cells of the row at time `t` that are unknown. Whatever these two cells are, the
row at time `t` alternates again, with the same phase, from four cells further on (`back_step_gen`,
for any alternating word and any diagram obeying `LeftPerm`; `heal4` and `heal5` are the two finite
checks behind it). The far end of the block moves one cell further left. After
`s` steps the row at time `a - s` alternates on `[4 s, L - 1 + s]` (`back_iter_gen`, `back_iter`).

*The edge.* At every time `t ≥ 1` the two leftmost black cells of the row are adjacent:
`cell t (-t) = cell t (-(t - 1)) = true` (`Rule30Jen.cell_left_edge`, `Rule30Diagonals.D_one`), so
no alternating block contains both (`edge_pair`). With `s = ⌊(a - 1)/5⌋` the block
`[4 s, L - 1 + s]` at time `a - s` contains both as soon as `L ≥ a - 2 s + 1`. The same two steps
applied to any alternating block give `alt_block`, and applied to `evol x` they give
`black_run_evol` (`Rule30FiniteConfigs.evol_left_edge`, `Rule30CenterRuns.evol_left_edge_succ`).

*White runs.* `Rule30CenterRuns.pre_triangle` at time `a` gives `cell a (-k) = [k odd]` for
`ℓ + 2 ≤ k < L` (`preRow_large`), and the same argument applies to this block of the other phase.

*White cells.* A white cell in every window `[a, (8 a + 10) / 5]` gives the times
`gW 0 = 1`, `gW (m + 1) = gW m + ⌊(3 gW m + 11) / 5⌋ + 1`, each with one more white cell before it
(`whiteCount_gW`), and `5^m (3 gW m + 16) ≤ 19 · 8^m` (`gW_bound`).

**Antecedents in the catalog.** `Rule30CenterRuns` proves `L ≤ a` for black runs, `L ≤ a - 3` for
white runs from `a ≥ 3`, and `⌊log₄ n⌋` white cells before `n`, from the same alternating row
(`black_triangle`, `pre_triangle`) and the left-edge diagonals. The healing distance `4` is already
in `Rule30ZeroBoundaryStripe.agrees_pre` and `agrees_pre_run`: for a left half-row with a zero
boundary, a preimage of a row that agrees with the stripe from depth `L` on agrees with it from
depth `L + 4` on, and from depth `L + 4 t` on after `t` steps back. `back_step_gen` is the variant
for a finite block, whose far end grows by one cell per step back, in any diagram that obeys
rule 30's left-permutivity. What is new here is the combination of this backward healing with the
adjacent black pair of the left edge.

**Not claimed.**
* No bound of slope `< 1` for white runs. `white_run_front` and `white_run_five_le` depend on `ℓ`,
  and nothing here bounds `ℓ` by a fraction of `a`; `white_run_after_nine_black` assumes nine black
  cells right before the run.
* Nothing sublinear. The slope `3/5` is the limit of this method: it uses only the healing distance
  `4` per step and the two cells `D 0 = D 1 = 1` of the left edge. The following computations,
  made outside Lean and not formalized here, support this. Over all `4^s` choices of the two
  unknown cells along `s` steps back from a long alternating block, exactly `40 · 4^(s - 4)`
  chains, that is `5/32` of them, move the near end of the block by the full `4 s` (checked for
  `4 ≤ s ≤ 9`), and no cell outside the block given by `back_iter_gen` is forced. In the center
  column before time `10^7`, `max (5 L - 3 a)` over black runs is `6`, at `a = 3`.
-/

namespace Rule30Submission

open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize Rule30Diagonals Rule30BlackRuns Rule30CenterRuns

/-! ### Reading a row leftward -/

/-- A space-time diagram that obeys rule 30's leftward reconstruction (left-permutivity). Both the
single-seed diagram `cell` and every evolution `evol x` do. -/
def LeftPerm (F : Nat → Int → Bool) : Prop :=
  ∀ t i, F t (i - 1) = xor (F (t + 1) i) (F t i || F t (i + 1))

theorem leftPerm_cell : LeftPerm cell := cell_left

theorem leftPerm_evol (x : Int → Bool) : LeftPerm (Rule30Realization.evol x) :=
  Rule30FiniteConfigs.evol_left x

/-- An alternating word, of either phase. -/
def Alternating (A : Nat → Bool) : Prop := ∀ k, A (k + 1) = !A k

theorem alternating_ev (φ : Nat) : Alternating (fun k => ev (k + φ)) := fun k => by
  show ev (k + 1 + φ) = !ev (k + φ)
  rw [Nat.add_right_comm, ev_succ]

theorem Alternating.succ_ne {A : Nat → Bool} (hA : Alternating A) (k : Nat) : A (k + 1) ≠ A k := by
  rw [hA k]; cases A k <;> decide

/-! ### Backward healing of the alternating block -/

/-- Five cells of the preimage heal any defect: the two unknown cells `u`, `v` do not matter. -/
theorem heal4 (b u v y1 y2 y3 y4 : Bool) (e1 : y1 = xor b (v || u)) (e2 : y2 = xor (!b) (y1 || v))
    (e3 : y3 = xor b (y2 || y1)) (e4 : y4 = xor (!b) (y3 || y2)) : y4 = b := by
  subst e1 e2 e3 e4; cases b <;> cases u <;> cases v <;> rfl

theorem heal5 (b u v y1 y2 y3 y4 y5 : Bool) (e1 : y1 = xor b (v || u))
    (e2 : y2 = xor (!b) (y1 || v)) (e3 : y3 = xor b (y2 || y1)) (e4 : y4 = xor (!b) (y3 || y2))
    (e5 : y5 = xor b (y4 || y3)) : y5 = !b := by
  subst e1 e2 e3 e4 e5; cases b <;> cases u <;> cases v <;> rfl

/-- **One step back.** If the row at time `t + 1` reads an alternating word `A` on `[r, l]`
(`F (t + 1) (i - k) = A k`), then the row at time `t` reads `A` on `[r + 4, l + 1]`, whatever the
rest of the row is. Stated for any `F` obeying the left-permutive identity of rule 30, with cells
counted leftward from a column `i`. -/
theorem back_step_gen (F : Nat → Int → Bool) (hF : LeftPerm F) {A : Nat → Bool} (hA : Alternating A)
    (i : Int) (t r l : Nat) (h : ∀ k, r ≤ k → k ≤ l → F (t + 1) (i - (k : Int)) = A k) :
    ∀ k, r + 4 ≤ k → k ≤ l + 1 → F t (i - (k : Int)) = A k := by
  -- cell `k + 1` of row `t` from cells `k`, `k - 1` of row `t` and cell `k` of row `t + 1`
  have step : ∀ k, r ≤ k → k ≤ l →
      F t (i - ((k + 1 : Nat) : Int)) = xor (A k) (F t (i - (k : Int)) || F t (i - (k : Int) + 1)) := by
    intro k h1 h2
    rw [← h k h1 h2, ← hF t (i - (k : Int))]
    exact congrArg (F t) (by omega)
  have step2 : ∀ k, r ≤ k + 1 → k + 1 ≤ l → F t (i - ((k + 2 : Nat) : Int)) =
      xor (A (k + 1)) (F t (i - ((k + 1 : Nat) : Int)) || F t (i - (k : Int))) := by
    intro k h1 h2
    rw [step (k + 1) h1 h2, show i - ((k + 1 : Nat) : Int) + 1 = i - (k : Int) by omega]
  have hA' : ∀ k, A (k + 1) = !A k := hA
  -- the cells `r + 4` and `r + 5` are healed, whatever the cells `r - 1` and `r` are
  have base4 : r + 3 ≤ l → F t (i - ((r + 4 : Nat) : Int)) = A (r + 4) := by
    intro hl
    have e1 := step r (Nat.le_refl r) (by omega)
    have e2 := step2 r (by omega) (by omega)
    have e3 := step2 (r + 1) (by omega) (by omega)
    have e4 := step2 (r + 2) (by omega) (by omega)
    simp only [hA', Bool.not_not] at e2 e3 e4 ⊢
    exact heal4 _ _ _ _ _ _ _ e1 e2 e3 e4
  have base5 : r + 4 ≤ l → F t (i - ((r + 5 : Nat) : Int)) = A (r + 5) := by
    intro hl
    have e1 := step r (Nat.le_refl r) (by omega)
    have e2 := step2 r (by omega) (by omega)
    have e3 := step2 (r + 1) (by omega) (by omega)
    have e4 := step2 (r + 2) (by omega) (by omega)
    have e5 := step2 (r + 3) (by omega) (by omega)
    simp only [hA', Bool.not_not] at e2 e3 e4 e5 ⊢
    exact heal5 _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5
  -- two healed neighbours give the next cell
  have prop : ∀ k, r ≤ k + 1 → k + 1 ≤ l → F t (i - (k : Int)) = A k →
      F t (i - ((k + 1 : Nat) : Int)) = A (k + 1) → F t (i - ((k + 2 : Nat) : Int)) = A (k + 2) := by
    intro k hk1 hk2 h0 h1
    rw [step2 k hk1 hk2, h1, h0, hA (k + 1), hA k]
    cases A k <;> rfl
  have pairs : ∀ n, (r + 4 + n ≤ l + 1 → F t (i - ((r + 4 + n : Nat) : Int)) = A (r + 4 + n)) ∧
      (r + 5 + n ≤ l + 1 → F t (i - ((r + 5 + n : Nat) : Int)) = A (r + 5 + n)) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => base4 (by omega), fun _ => base5 (by omega)⟩
    | succ n ih =>
      have h0 := ih.1
      have h1 := ih.2
      rw [show r + 5 + n = r + 4 + n + 1 by omega] at h1
      rw [show r + 4 + (n + 1) = r + 4 + n + 1 by omega, show r + 5 + (n + 1) = r + 4 + n + 2 by omega]
      exact ⟨fun hl => h1 (by omega),
        fun hl => prop (r + 4 + n) (by omega) (by omega) (h0 (by omega)) (h1 (by omega))⟩
  intro k hk1 hk2
  have := (pairs (k - (r + 4))).1 (by omega)
  rwa [show r + 4 + (k - (r + 4)) = k by omega] at this

/-- **`s` steps back.** An alternating block on `[r, l]` at time `a` forces the same alternating
word on `[r + 4 s, l + s]` at time `a - s`. -/
theorem back_iter_gen (F : Nat → Int → Bool) (hF : LeftPerm F) {A : Nat → Bool} (hA : Alternating A)
    (i : Int) (a r l : Nat) (h : ∀ k, r ≤ k → k ≤ l → F a (i - (k : Int)) = A k) :
    ∀ s, s ≤ a → ∀ k, r + 4 * s ≤ k → k ≤ l + s → F (a - s) (i - (k : Int)) = A k
  | 0, _, k, h1, h2 => by
    rw [Nat.sub_zero]
    exact h k (by omega) (by omega)
  | s + 1, hs, k, h1, h2 => by
    have ih := back_iter_gen F hF hA i a r l h s (by omega)
    rw [show a - s = (a - (s + 1)) + 1 by omega] at ih
    exact back_step_gen F hF hA i (a - (s + 1)) (r + 4 * s) (l + s) ih k (by omega) (by omega)

/-- `back_iter_gen` for the single-cell diagram, from the center column. -/
theorem back_iter {A : Nat → Bool} (hA : Alternating A) (a r l : Nat)
    (h : ∀ k, r ≤ k → k ≤ l → cell a (-(k : Int)) = A k) :
    ∀ s, s ≤ a → ∀ k, r + 4 * s ≤ k → k ≤ l + s → cell (a - s) (-(k : Int)) = A k := by
  intro s hs k h1 h2
  have := back_iter_gen cell leftPerm_cell hA 0 a r l
    (fun k h1 h2 => by rw [Int.zero_sub]; exact h k h1 h2) s hs k h1 h2
  rwa [Int.zero_sub] at this

/-! ### The left edge -/

/-- **No alternating block covers the two leftmost black cells.** At time `t ≥ 1` the cells
`-t` and `-(t - 1)` are both black. -/
theorem edge_pair (t : Nat) {A : Nat → Bool} (hA : Alternating A) (ht : 1 ≤ t)
    (h0 : cell t (-(t : Int)) = A t) (h1 : cell t (-((t - 1 : Nat) : Int)) = A (t - 1)) : False := by
  rw [cell_left_edge] at h0
  have hD : D 1 t = true := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    exact D_one t'
  have e : cell t (-((t - 1 : Nat) : Int)) = D 1 t := cell_congr (by omega)
  rw [e, hD] at h1
  apply hA.succ_ne (t - 1)
  rw [show t - 1 + 1 = t by omega, ← h0, ← h1]

/-! ### Black runs of the center column -/

/-- **A black run of the center column starting at time `a ≥ 1` has length at most
`a - 2 ⌊(a - 1) / 5⌋`.** -/
theorem black_run_three_fifths (a L : Nat) (ha : 1 ≤ a)
    (h : ∀ i, i < L → center (a + i) = true) : L + 2 * ((a - 1) / 5) ≤ a := by
  obtain ⟨s, hs⟩ : ∃ s, s = (a - 1) / 5 := ⟨_, rfl⟩
  rw [← hs]
  refine Classical.byContradiction fun hcon => ?_
  have row : ∀ k, 0 ≤ k → k ≤ L - 1 → cell a (-(k : Int)) = ev k :=
    fun k _ hk => black_triangle a L h k a (Nat.le_refl a) (by omega)
  have back := back_iter (A := ev) ev_succ a 0 (L - 1) row s (by omega)
  exact edge_pair (a - s) (A := ev) ev_succ (by omega) (back (a - s) (by omega) (by omega))
    (back (a - s - 1) (by omega) (by omega))

/-- **Slope `3/5` for black runs:** `5 L ≤ 3 a + 10`. -/
theorem black_run_five_le (a L : Nat) (ha : 1 ≤ a)
    (h : ∀ i, i < L → center (a + i) = true) : 5 * L ≤ 3 * a + 10 := by
  have := black_run_three_fifths a L ha h
  omega

/-! ### Alternating blocks anywhere -/

/-- **Alternating blocks stay away from the left edge.** If at time `t` the row reads an
alternating word, of either phase, on the cells `-m, …, -r` with `m ≤ t`, then
`5 m ≤ 3 t + 2 r + 6`. In diagonal coordinates `d = t - k`: a block whose right end is on diagonal
`d₂` starts on a diagonal `d₁ ≥ (2 d₂ - 6) / 5`. -/
theorem alt_block {A : Nat → Bool} (hA : Alternating A) (t r m : Nat) (hmt : m ≤ t)
    (h : ∀ k, r ≤ k → k ≤ m → cell t (-(k : Int)) = A k) : 5 * m ≤ 3 * t + 2 * r + 6 := by
  refine Classical.byContradiction fun hcon => ?_
  obtain ⟨s, hs⟩ : ∃ s : Nat, s = (t - m + 1) / 2 := ⟨_, rfl⟩
  have back := back_iter hA t r m h s (by omega)
  exact edge_pair (t - s) hA (by omega) (back (t - s) (by omega) (by omega))
    (back (t - s - 1) (by omega) (by omega))

/-! ### White runs -/

/-- Beyond the first black cell, the forced row of a white run alternates with odd cells black. -/
theorem preRow_large (k ℓ : Nat) (hk : ℓ + 2 ≤ k) : preRow k ℓ = ev (k + 1) := by
  unfold preRow ev
  by_cases hp : k % 2 = 1
  · rw [decide_eq_true ⟨by omega, Or.inl hp⟩, decide_eq_true (by omega)]
  · rw [decide_eq_false (by omega), decide_eq_false (by omega)]

/-- **White runs, relative to the right front.** If at the start `a ≥ 1` of a white run of length
`L` the first black cell right of the center is at column `ℓ + 1`, then
`L ≤ a - 2 ⌊(a - ℓ - 3) / 5⌋`. -/
theorem white_run_front (a L ℓ : Nat) (ha : 1 ≤ a) (h : ∀ i, i < L → center (a + i) = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    L + 2 * ((a - ℓ - 3) / 5) ≤ a := by
  obtain ⟨s, hs⟩ : ∃ s, s = (a - ℓ - 3) / 5 := ⟨_, rfl⟩
  rw [← hs]
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · have := white_run_le' a L ha h
    omega
  refine Classical.byContradiction fun hcon => ?_
  have hcol := col_one a ℓ L h hw hb
  have row : ∀ k, ℓ + 2 ≤ k → k ≤ L - 1 → cell a (-(k : Int)) = ev (k + 1) := by
    intro k hk1 hk2
    rw [pre_triangle a ℓ L h hcol k a (Nat.le_refl a) (by omega), show a + ℓ - a = ℓ by omega]
    exact preRow_large k ℓ hk1
  have back := back_iter (alternating_ev 1) a (ℓ + 2) (L - 1) row s (by omega)
  exact edge_pair (a - s) (alternating_ev 1) (by omega) (back (a - s) (by omega) (by omega))
    (back (a - s - 1) (by omega) (by omega))

/-- **White runs, given the front:** `5 L ≤ 3 a + 2 ℓ + 14`. -/
theorem white_run_five_le (a L ℓ : Nat) (ha : 1 ≤ a) (h : ∀ i, i < L → center (a + i) = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    5 * L ≤ 3 * a + 2 * ℓ + 14 := by
  have := white_run_front a L ℓ ha h hw hb
  have := white_run_le' a L ha h
  omega

/-- Every white run starting at `a ≥ 1` has a right front `ℓ + 1` with the bound above. -/
theorem white_run_exists_front (a L : Nat) (ha : 1 ≤ a)
    (h : ∀ i, i < L → center (a + i) = false) :
    ∃ ℓ, (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) ∧ cell a ((ℓ + 1 : Nat) : Int) = true ∧
      L + 2 * ((a - ℓ - 3) / 5) ≤ a := by
  obtain ⟨ℓ, hw, hb⟩ := first_black a ha
  exact ⟨ℓ, hw, hb, white_run_front a L ℓ ha h hw hb⟩

/-- **A white run that starts at time `a` right after nine black cells
(`c (a - 9) = … = c (a - 1) = 1`) has length `L` with `5 L ≤ 3 a + 16`.**
`Rule30BlackRuns.nine_black` puts the first black cell right of the center at column `2`, so
`ℓ = 1` in `white_run_five_le`. -/
theorem white_run_after_nine_black (a L : Nat) (ha : 9 ≤ a)
    (hb : ∀ s, s < 9 → center (a - 9 + s) = true) (h : ∀ i, i < L → center (a + i) = false) :
    5 * L ≤ 3 * a + 16 := by
  have hb' : ∀ s, s < 9 → cell (a - 9 + s) 0 = true := hb
  obtain ⟨n1, n2⟩ := Rule30BlackRuns.nine_black (a - 9) 0 hb'
  rw [show a - 9 + 9 = a by omega] at n1 n2
  obtain ⟨ℓ, hw, hbl, _⟩ := white_run_exists_front a L (by omega) h
  rcases Nat.lt_or_ge ℓ 1 with h0 | h1
  · have e : cell a ((ℓ + 1 : Nat) : Int) = cell a ((0 : Int) + 1) := cell_congr (by omega)
    rw [e, n1] at hbl
    exact absurd hbl (by decide)
  rcases Nat.lt_or_ge ℓ 2 with h2 | h2
  · have := white_run_five_le a L ℓ (by omega) h hw hbl
    omega
  · have := hw 2 (by omega) h2
    have e : cell a ((2 : Nat) : Int) = cell a ((0 : Int) + 2) := cell_congr (by omega)
    rw [e, n2] at this
    exact absurd this (by decide)

/-! ### Every column of every configuration with a leftmost black cell -/

section General
open Rule30Realization Rule30FiniteConfigs

/-- **The slope `3/5` for any column of any configuration with a leftmost black cell `lo`.**
Let `e = a + i - lo` be the time since the left edge passed column `i`. For every `s < a` with
`5 s + 1 ≤ e`, a black run of column `i` starting at time `a` has length `L ≤ e - 2 s`. For the
center column of the single black cell (`lo = i = 0`), `s = ⌊(a - 1) / 5⌋` gives
`black_run_three_fifths`. -/
theorem black_run_evol {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (i : Int) (a L s : Nat) (hs : s < a)
    (he : 5 * (s : Int) + 1 ≤ a + i - lo) (h : ∀ j, j < L → evol x (a + j) i = true) :
    (L : Int) + 2 * s ≤ a + i - lo := by
  refine Classical.byContradiction fun hcon => ?_
  have row : ∀ k, 0 ≤ k → k ≤ L - 1 → evol x a (i - (k : Int)) = ev k :=
    fun k _ hk => black_triangle_evol x i a L h k a (Nat.le_refl a) (by omega)
  have back := back_iter_gen (evol x) (leftPerm_evol x) (A := ev) ev_succ i a 0 (L - 1) row s
    (by omega)
  -- the two leftmost black cells at time `a - s` are the cells `ke` and `ke - 1` left of `i`
  obtain ⟨ke, hke⟩ : ∃ ke : Nat, (ke : Int) = i - lo + (a - s : Nat) :=
    ⟨(i - lo + (a - s : Nat)).toNat, by omega⟩
  have h0 := back ke (by omega) (by omega)
  have h1 := back (ke - 1) (by omega) (by omega)
  rw [show i - (ke : Int) = lo - ((a - s : Nat) : Int) by omega,
    evol_left_edge hlo hzero (a - s)] at h0
  obtain ⟨t', ht'⟩ : ∃ t', a - s = t' + 1 := ⟨a - s - 1, by omega⟩
  rw [ht', show i - ((ke - 1 : Nat) : Int) = lo - ((t' + 1 : Nat) : Int) + 1 by omega,
    evol_left_edge_succ hlo hzero t'] at h1
  apply (show Alternating ev from ev_succ).succ_ne (ke - 1)
  rw [show ke - 1 + 1 = ke by omega, ← h0, ← h1]

end General

/-! ### White cells recur faster -/

/-- Every window `[a, (8 a + 10) / 5]`, `a ≥ 1`, holds a white cell of the center column. -/
theorem exists_white_three_fifths (a : Nat) (ha : 1 ≤ a) :
    ∃ t, a ≤ t ∧ 5 * t ≤ 8 * a + 10 ∧ center t = false := by
  refine Classical.byContradiction fun hcon => ?_
  have h : ∀ i, i < (3 * a + 10) / 5 + 1 → center (a + i) = true := by
    intro i hi
    cases hc : center (a + i)
    · exact absurd ⟨a + i, by omega, by omega, hc⟩ hcon
    · rfl
  have := black_run_five_le a _ ha h
  omega

/-- For `a ≥ 6`, every window `[a, 2 a)` holds a white cell. -/
theorem exists_white_two (a : Nat) (ha : 6 ≤ a) : ∃ t, a ≤ t ∧ t < 2 * a ∧ center t = false := by
  obtain ⟨t, h1, h2, h3⟩ := exists_white_three_fifths a (by omega)
  exact ⟨t, h1, by omega, h3⟩

/-- The times `gW 0 = 1`, `gW (m + 1) = gW m + ⌊(3 gW m + 11)/5⌋ + 1`. -/
def gW : Nat → Nat
  | 0 => 1
  | m + 1 => gW m + (3 * gW m + 11) / 5 + 1

theorem gW_pos : ∀ m, 1 ≤ gW m
  | 0 => Nat.le_refl 1
  | m + 1 => by have := gW_pos m; simp only [gW]; omega

/-- Each time `gW (m + 1)` has one more white cell before it than `gW m`. -/
theorem whiteCount_gW : ∀ m, m ≤ whiteCount (gW m)
  | 0 => Nat.zero_le _
  | m + 1 => by
    obtain ⟨t, h1, h2, h3⟩ := exists_white_three_fifths (gW m) (gW_pos m)
    have := whiteCount_lt (b := gW (m + 1)) h1 (by simp only [gW]; omega) h3
    have ih := whiteCount_gW m
    omega

theorem gW_bound : ∀ m, 5 ^ m * (3 * gW m + 16) ≤ 19 * 8 ^ m
  | 0 => by decide
  | m + 1 => by
    have ih := gW_bound m
    have e : 5 * (3 * gW (m + 1) + 16) ≤ 8 * (3 * gW m + 16) := by simp only [gW]; omega
    have h1 : 5 ^ (m + 1) * (3 * gW (m + 1) + 16) = 5 ^ m * (5 * (3 * gW (m + 1) + 16)) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have h3 : 19 * 8 ^ (m + 1) = 8 * (19 * 8 ^ m) := by
      rw [Nat.pow_succ, Nat.mul_comm (8 ^ m) 8, Nat.mul_left_comm]
    rw [h1, h3]
    calc 5 ^ m * (5 * (3 * gW (m + 1) + 16)) ≤ 5 ^ m * (8 * (3 * gW m + 16)) :=
          Nat.mul_le_mul_left _ e
      _ = 8 * (5 ^ m * (3 * gW m + 16)) := Nat.mul_left_comm _ _ _
      _ ≤ 8 * (19 * 8 ^ m) := Nat.mul_le_mul_left 8 ih

/-- **Before time `n` the center column has at least `m` white cells whenever
`19 · 8^m ≤ 5^m · (3 n + 16)`**, that is `whiteCount n ≥ log_{8/5} ((3 n + 16) / 19)`. This improves
`Rule30CenterRuns.log_le_whiteCount` (`⌊log₄ n⌋`). -/
theorem whiteCount_eight_fifths (m n : Nat) (h : 19 * 8 ^ m ≤ 5 ^ m * (3 * n + 16)) :
    m ≤ whiteCount n := by
  have hb := gW_bound m
  have hp : 0 < 5 ^ m := Nat.pow_pos (by decide)
  have hle : 3 * gW m + 16 ≤ 3 * n + 16 := Nat.le_of_mul_le_mul_left (Nat.le_trans hb h) hp
  exact Nat.le_trans (whiteCount_gW m) (whiteCount_mono _ _ (by omega))

theorem whiteCount_eight : whiteCount 8 = 3 := by decide

/-- **Before time `2^m` the center column has at least `m - 1` white cells** (at least `m` for
`m ≥ 3`). `Rule30CenterRuns.whiteCount_pow_four` gave `m` white cells before `4^m`. -/
theorem whiteCount_pow_two : ∀ m, m ≤ whiteCount (2 ^ m) + 1
  | 0 => Nat.zero_le _
  | 1 => by decide
  | 2 => by decide
  | 3 => by rw [show 2 ^ 3 = 8 by rfl, whiteCount_eight]; omega
  | m + 4 => by
    have hp : 6 ≤ 2 ^ (m + 3) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 3 ≤ m + 3 by omega)
      rw [show 2 ^ 3 = 8 by rfl] at this
      omega
    obtain ⟨t, h1, h2, h3⟩ := exists_white_two (2 ^ (m + 3)) hp
    have := whiteCount_lt (b := 2 ^ (m + 4)) h1 (by rw [Nat.pow_succ]; omega) h3
    have ih := whiteCount_pow_two (m + 3)
    omega

/-- `log₂ n ≤ whiteCount n + 1`, with core's `Nat.log2`. For small `n` this is better than
`whiteCount_eight_fifths`. -/
theorem log_two_le_whiteCount (n : Nat) : Nat.log2 n ≤ whiteCount n + 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rw [Nat.log2_zero]; exact Nat.zero_le _
  · have h1 := whiteCount_pow_two (Nat.log2 n)
    have h2 := whiteCount_mono _ _ (Nat.log2_self_le (by omega : n ≠ 0))
    omega

end Rule30Submission