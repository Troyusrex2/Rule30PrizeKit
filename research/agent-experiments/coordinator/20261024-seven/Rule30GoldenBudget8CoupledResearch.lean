import Rule30GoldenBudget8C600V2Research
import Rule30GoldenBudgetCoupledResearch

/-! Consequences of the independently checked, bounded budget-eight
certificate. These statements do not assert infinite support. -/

namespace Rule30GoldenBudget8CoupledResearch
open Ruliology.CellularAutomata
open Rule30GoldenBudgetCoupledResearch (evenCount count_history)

theorem psi_at_least_nine (R : Nat → Bool) :
    9 ≤ evenCount (Rule30PeriodTwoSideways.Psi R) 102 := by
  rw [←count_history (Rule30GoldenCoupledResearch.history_eq_alt R)]
  exact Rule30GoldenBudget8C600V2Research.minimum_nine _
    (Rule30GoldenCoupledResearch.golden_free R)

theorem no_alternation_with_eight_even_cells (T : Nat)
    (hb : evenCount (Rule30ZeroBoundary.leftRow T) 102 ≤ 8) :
    ¬ ∀ k, Rule30Jen.cell (T+2*k) 0=true ∧ Rule30Jen.cell (T+2*k+1) 0=false := by
  intro hT
  have hc := Rule30GoldenBudget8C600V2Research.minimum_nine _
    (Rule30GoldenHistoryResearch.golden_free hT)
  rw [count_history (Rule30GoldenHistoryResearch.history_eq_alt_free hT)] at hc
  omega

end Rule30GoldenBudget8CoupledResearch
