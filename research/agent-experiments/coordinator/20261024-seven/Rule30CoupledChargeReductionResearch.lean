import Rule30GoldenBudgetCoupledResearch

/-! A precise unbounded counting target. The reduction is proved; the
counting inequality is an explicit hypothesis, never a new axiom. -/

namespace Rule30CoupledChargeReductionResearch
open Ruliology.CellularAutomata
open Rule30GoldenDFAResearch (Golden)

def zeros (s : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => zeros s n+(!s n).toNat

theorem zeros_mono (s : Nat → Bool) {a b : Nat} (hab : a≤b) : zeros s a≤zeros s b := by
  induction b with
  | zero =>
    have ha : a=0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases h : a≤b
    · exact Nat.le_trans (ih h) (by rw [zeros];omega)
    · have he : a=b+1 := by omega
      subst a
      exact Nat.le_refl _

theorem false_among_five {s : Nat → Bool} (hg : Golden s) (k : Nat) :
    ∃ i, i<5 ∧ s (k+i)=false := by
  classical
  apply Classical.byContradiction
  intro hn
  have ht (i : Nat) (hi : i<5) : s (k+i)=true := by
    cases hs : s (k+i)
    · exact False.elim (hn ⟨i,hi,hs⟩)
    · rfl
  exact hg.2 k ⟨by simpa using ht 0 (by omega),ht 1 (by omega),ht 2 (by omega),
    ht 3 (by omega),ht 4 (by omega)⟩

theorem zeros_five {s : Nat → Bool} (hg : Golden s) (k : Nat) :
    zeros s k+1 ≤ zeros s (k+5) := by
  obtain ⟨i,hi,hf⟩ := false_among_five hg k
  have ha := zeros_mono s (show k≤k+i by omega)
  have hb := zeros_mono s (show k+i+1≤k+5 by omega)
  rw [zeros,hf] at hb
  simp only [Bool.not_false,Bool.toNat_true] at hb
  omega

theorem zeros_lower_bound {s : Nat → Bool} (hg : Golden s) (n : Nat) :
    n ≤ zeros s (5*n) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h := zeros_five hg (5*n)
    rw [show 5*(n+1)=5*n+5 by omega]
    omega

def Charge (C : Nat) (R : Nat → Bool) : Prop := ∀ n,
  zeros (Rule30GoldenCoupledResearch.free R) n ≤
    C*Rule30GoldenBudgetResearch.count (Rule30GoldenCoupledResearch.free R) n

theorem not_finSupp_psi_of_charge {C : Nat} {R : Nat → Bool} (hc : Charge C R) :
    ¬ Rule30ZeroBoundary.FinSupp (Rule30PeriodTwoSideways.Psi R) := by
  rintro ⟨W,hW⟩
  have hs : ∀ d, W≤d → Rule30GoldenEvenSupportResearch.code (Rule30GoldenCoupledResearch.free R) d=false := by
    intro d hd
    rw [Rule30GoldenHistoryResearch.history_code (Rule30GoldenCoupledResearch.history_eq_alt R)]
    exact hW (2*d+2) (by omega)
  have he := Rule30GoldenBudgetResearch.count_le_support hs (5*(C*W+1))
  have hz := zeros_lower_bound (Rule30GoldenCoupledResearch.golden_free R) (C*W+1)
  have hcharge := hc (5*(C*W+1))
  have hmul := Nat.mul_le_mul_left C he
  omega

theorem CQ01_of_charge (C : Nat)
    (hc : ∀ R, Rule30ZeroBoundary.FinSupp R → Charge C R) : Rule30PeriodTwoCoupled.CQ01 := by
  apply Rule30PeriodTwoSideways.CQ01_iff_Psi.mpr
  intro R hR
  exact not_finSupp_psi_of_charge (hc R hR)

end Rule30CoupledChargeReductionResearch
