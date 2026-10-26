import Rule30CoupledSixWordResearch

/-! The single-slip candidates suggested by CoinAIlyzer wiki cannot be actual
coupled free responses. This is a corollary of the earlier, attributed six-word
exclusion, not a new discovery of that exclusion. No finite-support premise is
needed: the obstruction applies to every right half, including infinite ones. -/
namespace Rule30SingleSlipExclusionResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30PeriodTwoSideways

def singleSlip (L s : Nat) : Bool := decide ((s + if L ≤ s then 1 else 0)%2=1)

theorem singleSlip_word (L : Nat) (hL : 4 ≤ L) (he : L%2=0) :
    singleSlip L (L-4)=false ∧ singleSlip L (L-4+1)=true ∧
    singleSlip L (L-4+2)=false ∧ singleSlip L (L-4+3)=true ∧
    singleSlip L (L-4+4)=true ∧ singleSlip L (L-4+5)=false := by
  have hv (i : Nat) (hi : i < 6) :
      singleSlip L (L-4+i) = decide (i=1 ∨ i=3 ∨ i=4) := by
    unfold singleSlip
    by_cases h : L ≤ L-4+i
    · rw [if_pos h]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
    · rw [if_neg h]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
  exact ⟨by simpa using hv 0 (by omega), by simpa using hv 1 (by omega),
    by simpa using hv 2 (by omega), by simpa using hv 3 (by omega),
    by simpa using hv 4 (by omega), by simpa using hv 5 (by omega)⟩

theorem no_right_half_single_slip (L : Nat) (hL : 4 ≤ L) (he : L%2=0)
    (R : Nat → Bool) :
    ¬ (∀ s, zrow (Psi R) (2*s+1) 1=singleSlip L s) := by
  intro h
  have hword := singleSlip_word L hL he
  apply Rule30CoupledSixWordResearch.psi_free_no010110 R (L-4)
  simpa only [h] using hword

theorem slip94_not_realizable (R : Nat → Bool) :
    ¬ (∀ s, zrow (Psi R) (2*s+1) 1=singleSlip 94 s) :=
  no_right_half_single_slip 94 (by omega) (by decide) R

end Rule30SingleSlipExclusionResearch
