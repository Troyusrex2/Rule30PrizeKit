import Rule30RoundTwoChargeTwoResearch
import Rule30CriticalChargeOneBridgeResearch

/-! Transfer the coefficient-two obstruction to the unchanged counting target
used by the earlier Golden/ScaleCharges route. No stream or index changes. -/
namespace Rule30RoundTwoChargeTwoBridgeResearch
open Ruliology.CellularAutomata
open Rule30CriticalChargeOneBridgeResearch (charge_definition zeros_definition blackCount_definition)
open Rule30RoundTwoChargeTwoEntryResearch (right)

theorem right_finite : Rule30ZeroBoundary.FinSupp right :=
  Rule30RoundTwoChargeTwoEntryResearch.right_finite

theorem free_stream (s : Nat) : Rule30GoldenCoupledResearch.free right s =
    Rule30RoundTwoChargeTwoEntryResearch.stream s :=
  Rule30RoundTwoChargeTwoEntryResearch.free_stream s

theorem coupled_scale_counts (k : Nat) :
    Rule30CoupledChargeReductionResearch.zeros (Rule30GoldenCoupledResearch.free right) (14*k+6)=7*k+3 ∧
    Rule30TotalSpatialChargeReductionResearch.blackCount (Rule30PeriodTwoSideways.Psi right)
      (2*(14*k+6)+1)=10*k+7 := by
  have h := Rule30RoundTwoChargeTwoResearch.coupled_scale_counts k
  constructor
  · rw [zeros_definition]; exact h.1
  · rw [blackCount_definition]; exact h.2

theorem coefficient_two_false (B : Nat) :
    ¬ Rule30GoldenCriticalDriftResearch.CriticalCharge 2 B right := by
  intro hc
  exact Rule30RoundTwoChargeTwoResearch.coefficient_two_false B ((charge_definition 2 B right).mp hc)

theorem minimum_integer_coefficient {C B : Nat}
    (hc : Rule30GoldenCriticalDriftResearch.CriticalCharge C B right) : 3≤C :=
  Rule30RoundTwoChargeTwoResearch.minimum_integer_coefficient ((charge_definition C B right).mp hc)

end Rule30RoundTwoChargeTwoBridgeResearch
