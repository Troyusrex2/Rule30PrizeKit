import Rule30GoldenBudgetDAG4Research
import Rule30GoldenCoupledResearch

/-! Population consequences for actual sideways rows. These are finite
lower bounds, not an infinite-support assertion. -/

namespace Rule30GoldenBudgetCoupledResearch
open Ruliology.CellularAutomata

def evenCount (L : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k+1 => evenCount L k+(L (2*k+2)).toNat

theorem count_history {L s : Nat → Bool}
    (hh : ∀ t, Rule30ZeroBoundary.zrow L t 1=Rule30ZeroBoundary.alt s t) (K : Nat) :
    Rule30GoldenBudgetResearch.count s K = evenCount L K := by
  induction K with
  | zero => rfl
  | succ K ih => rw [Rule30GoldenBudgetResearch.count,evenCount,ih,
      Rule30GoldenHistoryResearch.history_code hh K]

theorem psi_at_least_five (R : Nat → Bool) :
    5 ≤ evenCount (Rule30PeriodTwoSideways.Psi R) 50 := by
  rw [←count_history (Rule30GoldenCoupledResearch.history_eq_alt R)]
  exact Rule30GoldenBudgetDAG4Research.minimum_count _ (Rule30GoldenCoupledResearch.golden_free R)

theorem no_alternation_with_four_even_cells (T : Nat)
    (hb : evenCount (Rule30ZeroBoundary.leftRow T) 50 ≤ 4) :
    ¬ ∀ k, Rule30Jen.cell (T+2*k) 0=true ∧ Rule30Jen.cell (T+2*k+1) 0=false := by
  intro hT
  have hc := Rule30GoldenBudgetDAG4Research.minimum_count _ (Rule30GoldenHistoryResearch.golden_free hT)
  rw [count_history (Rule30GoldenHistoryResearch.history_eq_alt_free hT)] at hc
  omega

end Rule30GoldenBudgetCoupledResearch
