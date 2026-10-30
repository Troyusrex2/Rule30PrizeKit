module

public import Ruliology.CellularAutomata.Rule30BlackRunErosion
public import Ruliology.CellularAutomata.Rule30LeftUnbounded

/-!
# Rule30SettledBarrier

Settled white diagonals and their black companions bound actual center runs. Both linear run bounds admit every fixed additive margin at sufficiently late times.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SettledBarrier

open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize Rule30Diagonals Rule30CenterRuns
open Rule30BlackRunErosion Rule30LeftReset Rule30LeftUnbounded

theorem no_stripe_at_constant (t k : Nat) (b : Bool)
    (h0 : D k t = b) (h1 : D k (t + 1) = b)
    (hrow : ∀ i : Int, (k : Int) - t - 2 ≤ i → i ≤ (k : Int) - t →
      cell t i = alt i) : False := by
  have hc : D k t = alt ((k : Int) - t) := hrow _ (by omega) (by omega)
  have hnext : D k (t + 1) = !(alt ((k : Int) - t)) := by
    show rule (cell t ((k : Int) - (t + 1) - 1))
      (cell t ((k : Int) - (t + 1)))
      (cell t ((k : Int) - (t + 1) + 1)) = _
    rw [hrow _ (by omega) (by omega), hrow _ (by omega) (by omega),
      hrow _ (by omega) (by omega)]
    rw [show (k : Int) - (t + 1) - 1 = ((k : Int) - t - 1) - 1 by omega,
      show (k : Int) - (t + 1) = (k : Int) - t - 1 by omega,
      show (k : Int) - t - 1 + 1 = (k : Int) - t by omega]
    rw [alt_pred, alt_pred]
    unfold rule
    cases alt ((k : Int) - t) <;> rfl
  rw [h0] at hc
  rw [h1, ← hc] at hnext
  cases b <;> cases hnext

theorem black_run_at_white_depth (a L k T s r : Nat)
    (ha : a = k + 5 * s + r) (hT : T ≤ a - s)
    (hw : ∀ t, T ≤ t → D k t = false)
    (h : ∀ i, i < L → center (a + i) = true) :
    L ≤ 3 * s + r + 2 := by
  refine Classical.byContradiction fun hlarge => ?_
  have hb := black_block_back a L h s (by omega)
  apply no_stripe_at_constant (a - s) k false (hw _ hT) (hw _ (by omega))
  intro i hi1 hi2
  exact hb i (by omega) (by omega)

theorem black_run_bound_at_white (k T : Nat)
    (hw : ∀ t, T ≤ t → D k t = false)
    (a L : Nat) (ha : k ≤ a) (hT : 5 * T ≤ 4 * a + k)
    (h : ∀ i, i < L → center (a + i) = true) :
    5 * L + 3 * k ≤ 3 * a + 18 := by
  let s := (a - k) / 5
  let r := (a - k) % 5
  have hsplit : a = k + 5 * s + r := by dsimp [s, r]; omega
  have hr : r < 5 := by dsimp [r]; omega
  have htime : T ≤ a - s := by dsimp [s]; omega
  have hb := black_run_at_white_depth a L k T s r hsplit htime hw h
  omega

theorem black_run_margin_unbounded (M : Nat) :
    ∃ A, ∀ a, A ≤ a → ∀ L,
      (∀ i, i < L → center (a + i) = true) → 5 * L + M ≤ 3 * a := by
  obtain ⟨k, hk, T, hT⟩ := D_infinitely_many_white (M + 18)
  refine ⟨k + 5 * T, ?_⟩
  intro a ha L h
  have hb := black_run_bound_at_white k T hT a L (by omega) (by omega) h
  omega

theorem preRow_pair_pin (n ell : Nat) (hn : 2 ≤ n)
    (hw : preRow n ell = false) (hb : preRow (n - 2) ell = true) :
    ell + 3 = n := by
  have hp := preRow_eq_true hb
  have hz := preRow_eq_false hw
  omega

theorem white_run_pair_front (a L j ell : Nat) (hj : j + 2 ≤ a)
    (hlen : a - j < L)
    (hrow : ∀ n, n < L → cell a (-(n : Int)) = preRow n ell)
    (hw : D j a = false) (hb : D (j + 2) a = true) :
    ell + 3 = a - j := by
  have hz := hrow (a - j) hlen
  rw [cell_neg_eq_D a (a - j) (by omega),
    show a - (a - j) = j by omega, hw] at hz
  have hp := hrow ((a - j) - 2) (by omega)
  rw [cell_neg_eq_D a ((a - j) - 2) (by omega),
    show a - ((a - j) - 2) = j + 2 by omega, hb] at hp
  exact preRow_pair_pin (a - j) ell (by omega) hz.symm hp.symm

theorem white_run_bound_two_pairs (j k a L : Nat) (hjk : j < k) (hka : k + 2 ≤ a)
    (hwj : D j a = false) (hbj : D (j + 2) a = true)
    (hwk : D k a = false) (hbk : D (k + 2) a = true)
    (h : ∀ i, i < L → center (a + i) = false) :
    L + j ≤ a := by
  refine Classical.byContradiction fun hlarge => ?_
  obtain ⟨ell, hrow⟩ := row_at_start a L (by omega) h
  have hj := white_run_pair_front a L j ell (by omega) (by omega) hrow hwj hbj
  have hk := white_run_pair_front a L k ell hka (by omega) hrow hwk hbk
  omega

theorem white_run_margin_unbounded (M : Nat) :
    ∃ A, ∀ a, A ≤ a → ∀ L,
      (∀ i, i < L → center (a + i) = false) → L + M ≤ a := by
  obtain ⟨j, hj, hwj⟩ := D_infinitely_many_white M
  obtain ⟨k, hk, hwk⟩ := D_infinitely_many_white j
  obtain ⟨Tbj, hbj⟩ := D_black_after_white hwj
  obtain ⟨Tbk, hbk⟩ := D_black_after_white hwk
  obtain ⟨Twj, hwj⟩ := hwj
  obtain ⟨Twk, hwk⟩ := hwk
  refine ⟨k + 2 + Tbj + Tbk + Twj + Twk, ?_⟩
  intro a ha L h
  have hb := white_run_bound_two_pairs j k a L hk (by omega)
    (hwj a (by omega)) (hbj a (by omega))
    (hwk a (by omega)) (hbk a (by omega)) h
  omega

theorem center_run_margins_unbounded (M : Nat) :
    ∃ A, ∀ a, A ≤ a → ∀ L,
      ((∀ i, i < L → center (a + i) = true) → 5 * L + M ≤ 3 * a) ∧
      ((∀ i, i < L → center (a + i) = false) → L + M ≤ a) := by
  obtain ⟨Ab, hb⟩ := black_run_margin_unbounded M
  obtain ⟨Aw, hw⟩ := white_run_margin_unbounded M
  exact ⟨Ab + Aw, fun a ha L => ⟨hb a (by omega) L, hw a (by omega) L⟩⟩

end Ruliology.CellularAutomata.Rule30SettledBarrier
