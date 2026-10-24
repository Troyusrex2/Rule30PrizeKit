import Rule30Tail13Complete
import Rule30ExternalFiveTailAudit

/-! Completes all five-tail cases of Quint and Gemini's verified f177ae
submission by using the exception-free four-tail / tail-13 result. This is
not Q01 and does not cover arbitrary finite tails. -/

namespace Rule30TailFiveCompletionResearch

open Ruliology.CellularAutomata
open Rule30ZeroBoundaryStripeFront Rule30ZeroBoundary Rule30Tail13Completion
open Rule30Submission

theorem tail5_13_eq_tail4 (i : Nat) : tail5 13 i = tail4 13 i := by
  unfold tail5 tail4
  by_cases h4 : i < 4
  · rw [if_pos (by omega), if_pos h4]
  · rw [if_neg h4]
    by_cases h5 : i < 5
    · have hi : i = 4 := by omega
      subst i; decide
    · rw [if_neg h5]

theorem row5_13_eq_row4 (m : Nat) : row5 m 13 = row4 m 13 := by
  funext k
  unfold row5 row4
  split
  · rfl
  · exact tail5_13_eq_tail4 _

theorem tail5_27_shift (i : Nat) : tail5 27 (i+1) = tail4 13 i := by
  by_cases hi : i < 4
  · have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> decide
  · simp only [tail5, tail4, if_neg hi, if_neg (show ¬ (i+1 < 5) by omega)]

theorem row5_27_eq_row4 (m : Nat) (hq : m % 2 = 0) :
    row5 m 27 = row4 (m+1) 13 := by
  funext k
  by_cases hk : k ≤ m
  · simp only [row5, row4, if_pos hk, if_pos (show k ≤ m+1 by omega)]
  · by_cases hk1 : k ≤ m+1
    · have he : k = m+1 := by omega
      subst k
      simp only [row5, row4, if_neg (show ¬ (m+1 ≤ m) by omega),
        if_pos (show m+1 ≤ m+1 by omega)]
      rw [show m+1-m-1 = 0 by omega, stripe_add_mod m 0 1 hq]
      decide
    · simp only [row5, row4, if_neg hk, if_neg hk1]
      rw [show k-m-1 = (k-(m+1)-1)+1 by omega]
      exact tail5_27_shift _

theorem stripe_five_tail_complete (m : Nat) (v : Fin 32) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 7 ∧
      (∀ k, 1 ≤ k → k < d → row5 m v.val k = stripe k) ∧
      row5 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row5 m v.val) t 1 = false := by
  by_cases h : (v.val ≠ 13 ∨ m % 2 = 0) ∧ (v.val ≠ 27 ∨ m % 2 = 1)
  · obtain ⟨d, hd, hdm, hag, hdev, t, ht, he, hz⟩ := stripe_five_tail m v h
    exact ⟨d, hd, hdm, hag, hdev, t, by omega, he, hz⟩
  · by_cases hv13 : v.val = 13
    · have hq : m % 2 = 1 := by omega
      rw [hv13, row5_13_eq_row4]
      obtain ⟨hag, hdev, t, ht, he, hz⟩ := row4_13_all_odd m hq
      exact ⟨m+1, by omega, by omega, hag, hdev, t, by omega, he, hz⟩
    · have hv27 : v.val = 27 := by omega
      have hq : m % 2 = 0 := by omega
      rw [hv27, row5_27_eq_row4 m hq]
      obtain ⟨hag, hdev, t, ht, he, hz⟩ := row4_13_all_odd (m+1) (by omega)
      exact ⟨m+2, by omega, by omega, hag, hdev, t, by omega, he, hz⟩

end Rule30TailFiveCompletionResearch
