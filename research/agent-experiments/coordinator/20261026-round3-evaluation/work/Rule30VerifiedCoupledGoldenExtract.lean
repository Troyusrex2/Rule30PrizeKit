import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

/-! Exact theorem block extracted from R30-20261024-9d92a2, previously Lean
and Human Verified. Original submission authors: see provenance JSON.
The block is reused with attribution, not claimed as new research here. -/

namespace Rule30Submission
open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize Rule30PeriodTwoSideways Rule30ZeroBoundary Rule30PeriodTwoCoupled
open Rule30Ether (drv drv_col0)

theorem u_golden (R : Nat → Bool) (s : Nat) (h : u R s = true) : u R (s + 1) = false := by
  have h1 : drv altCol R (2 * s + 1) 1 = true := h
  have e1 : drv altCol R (2 * s + 2) 1 =
      rule (drv altCol R (2 * s + 1) 0) (drv altCol R (2 * s + 1) 1) (drv altCol R (2 * s + 1) 2) := rfl
  rw [drv_col0, altCol_odd, h1] at e1
  have h2 : drv altCol R (2 * s + 2) 1 = true := by rw [e1]; rfl
  have e2 : drv altCol R (2 * s + 3) 1 =
      rule (drv altCol R (2 * s + 2) 0) (drv altCol R (2 * s + 2) 1) (drv altCol R (2 * s + 2) 2) := rfl
  rw [drv_col0, show 2 * s + 2 = 2 * (s + 1) by omega, altCol_even,
    show 2 * (s + 1) = 2 * s + 2 by omega, h2] at e2
  unfold u
  rw [show 2 * (s + 1) + 1 = 2 * s + 3 by omega, e2]
  rfl

/-- Finite window of `drv c R` starting at column `p + 1` of length `n`. -/
def drvRow (c R : Nat → Bool) (t p : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => drv c R t (p + 1) :: drvRow c R t (p + 1) n

theorem length_drvRow (c R : Nat → Bool) (t : Nat) :
    ∀ (n p : Nat), (drvRow c R t p n).length = n
  | 0, _ => rfl
  | n + 1, p => by simp [drvRow, length_drvRow c R t n (p + 1)]

theorem stepRow_drvRow (c R : Nat → Bool) (t : Nat) : ∀ (n p : Nat),
    Rule30BlackRuns.stepRow (drv c R t p) (drvRow c R t p (n + 1)) = drvRow c R (t + 1) p n
  | 0, _ => rfl
  | n + 1, p => by
    show rule (drv c R t p) (drv c R t (p + 1)) (drv c R t (p + 2)) ::
        Rule30BlackRuns.stepRow (drv c R t (p + 1)) (drvRow c R t (p + 1) (n + 1)) =
      drv c R (t + 1) (p + 1) :: drvRow c R (t + 1) (p + 1) n
    rw [stepRow_drvRow c R t n (p + 1)]
    rfl

theorem col1_drvRow (R : Nat → Bool) : ∀ (cs : List Bool) (t n : Nat),
    (∀ i, (hi : i < cs.length) → drv altCol R (t + i) 0 = cs[i]) →
    Rule30PeriodTwo.col1 cs (drvRow altCol R t 0 (n + cs.length + 1)) =
      (List.range cs.length).map (fun i => drv altCol R (t + i) 1)
  | [], t, n, _ => rfl
  | c :: cs, t, n, h => by
    have h0 : drv altCol R t 0 = c := h 0 (by simp)
    have hs : Rule30BlackRuns.stepRow c (drvRow altCol R t 0 ((n + cs.length + 1) + 1)) =
        drvRow altCol R (t + 1) 0 (n + cs.length + 1) := by
      rw [← h0]; exact stepRow_drvRow altCol R t (n + cs.length + 1) 0
    have ih := col1_drvRow R cs (t + 1) n (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show t + 1 + i = t + (i + 1) by omega]
      simpa using this)
    show (drvRow altCol R t 0 (n + (cs.length + 1) + 1)).headD false ::
        Rule30PeriodTwo.col1 cs (Rule30BlackRuns.stepRow c (drvRow altCol R t 0 (n + (cs.length + 1) + 1))) =
      (List.range (cs.length + 1)).map (fun i => drv altCol R (t + i) 1)
    rw [show n + (cs.length + 1) + 1 = (n + cs.length + 1) + 1 by omega, hs, ih,
      List.range_succ_eq_map]
    simp only [drvRow, List.headD_cons, List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [show t + 1 + i = t + (i + 1) by omega]

/-- **Five-step rule for `u R` from `s = 0`.** For every right half `R : Nat → Bool` and every `s`,
at least one of the five consecutive values `u R (s + i)` (`i < 5`) is `true`. -/
theorem u_black_among_five (R : Nat → Bool) (s : Nat) :
    ∃ i, i < 5 ∧ u R (s + i) = true := by
  have hc : ∀ i, (hi : i < (Rule30PeriodTwo.alt 9).length) →
      drv altCol R (2 * s + 1 + i) 0 = (Rule30PeriodTwo.alt 9)[i] := by
    intro i hi
    simp only [Rule30PeriodTwo.alt, List.getElem_map, List.getElem_range]
    rw [drv_col0]
    unfold altCol
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · have h1 : (2 * s + 1 + i) % 2 = 1 := by omega
      simp [h, h1]
    · have h1 : (2 * s + 1 + i) % 2 = 0 := by omega
      simp [h, h1]
  have hw := col1_drvRow R (Rule30PeriodTwo.alt 9) (2 * s + 1) 1 hc
  rw [Rule30PeriodTwo.alt_length] at hw
  have hmem : drvRow altCol R (2 * s + 1) 0 (1 + 9 + 1) ∈ allLists 11 := by
    have := mem_allLists (drvRow altCol R (2 * s + 1) 0 11)
    rwa [length_drvRow] at this
  have hck := List.all_eq_true.1 col1_five_check _ hmem
  rw [hw] at hck
  have hv : ∀ i, i < 9 →
      ((List.range 9).map (fun i => drv altCol R (2 * s + 1 + i) 1)).getD i false =
        drv altCol R (2 * s + 1 + i) 1 := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, hi]
  unfold blackAmongFive at hck
  rw [hv 0 (by omega), hv 2 (by omega), hv 4 (by omega), hv 6 (by omega), hv 8 (by omega)] at hck
  simp only [Bool.or_eq_true] at hck
  rcases hck with (((h0 | h2) | h4) | h6) | h8
  · exact ⟨0, by omega, by unfold u; rw [show 2 * (s + 0) + 1 = 2 * s + 1 + 0 by omega]; exact h0⟩
  · exact ⟨1, by omega, by unfold u; rw [show 2 * (s + 1) + 1 = 2 * s + 1 + 2 by omega]; exact h2⟩
  · exact ⟨2, by omega, by unfold u; rw [show 2 * (s + 2) + 1 = 2 * s + 1 + 4 by omega]; exact h4⟩
  · exact ⟨3, by omega, by unfold u; rw [show 2 * (s + 3) + 1 = 2 * s + 1 + 6 by omega]; exact h6⟩
  · exact ⟨4, by omega, by unfold u; rw [show 2 * (s + 4) + 1 = 2 * s + 1 + 8 by omega]; exact h8⟩

/-- **The free bits of `Psi R` contain no `00` and no `11111` at any step `s ≥ 0`.** -/
theorem Psi_free_no00_no11111 (R : Nat → Bool) (s : Nat) :
    ¬ (zrow (Psi R) (2 * s + 1) 1 = false ∧ zrow (Psi R) (2 * (s + 1) + 1) 1 = false) ∧
    ¬ ∀ i, i < 5 → zrow (Psi R) (2 * (s + i) + 1) 1 = true := by
  refine ⟨fun ⟨h0, h1⟩ => ?_, fun hall => ?_⟩
  · rw [Psi_free] at h0 h1
    have hu0 : u R s = true := by unfold u; revert h0; cases drv altCol R (2 * s + 1) 1 <;> decide
    have hu1 : u R (s + 1) = true := by unfold u; revert h1; cases drv altCol R (2 * (s + 1) + 1) 1 <;> decide
    have := u_golden R s hu0
    rw [hu1] at this
    exact absurd this (by decide)
  · obtain ⟨i, hi, hub⟩ := u_black_among_five R s
    have hpsi := hall i hi
    rw [Psi_free] at hpsi
    unfold u at hub
    rw [hub] at hpsi
    exact absurd hpsi (by decide)


end Rule30Submission
