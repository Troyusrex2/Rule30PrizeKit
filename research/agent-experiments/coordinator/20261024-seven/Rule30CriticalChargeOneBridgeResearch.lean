import Rule30CriticalChargeOneCoreResearch
import Rule30GoldenCriticalDriftResearch

/-! The standalone, official-import-only counterexample uses exactly the
previous research counting target. This bridge changes no index, count,
free stream, additive allowance, or quantifier. -/

namespace Rule30CriticalChargeOneBridgeResearch
open Ruliology.CellularAutomata
open Rule30GoldenCriticalDriftResearch (CriticalCharge)
open Rule30TotalSpatialChargeReductionResearch (blackCount)
open Rule30CoupledChargeReductionResearch (zeros)

abbrev right := Rule30CriticalChargeOneCoreResearch.right

theorem zeros_definition (s : Nat → Bool) (n : Nat) :
    zeros s n = Rule30CriticalChargeOneCoreResearch.zeros s n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zeros,Rule30CriticalChargeOneCoreResearch.zeros,ih]

theorem blackCount_definition (L : Nat → Bool) (n : Nat) :
    blackCount L n = Rule30CriticalChargeOneCoreResearch.blackCount L n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [blackCount,Rule30CriticalChargeOneCoreResearch.blackCount,ih]

theorem charge_definition (C B : Nat) (R : Nat → Bool) :
    CriticalCharge C B R ↔ Rule30CriticalChargeOneCoreResearch.CriticalCharge C B R := by
  unfold CriticalCharge Rule30CriticalChargeOneCoreResearch.CriticalCharge
  constructor
  · intro hc n
    have h := hc n
    rw [zeros_definition,blackCount_definition] at h
    exact h
  · intro hc n
    rw [zeros_definition,blackCount_definition]
    exact hc n

theorem right_finite : Rule30ZeroBoundary.FinSupp right := Rule30CriticalChargeOneCoreResearch.right_finite

theorem free_stream (s : Nat) :
    Rule30GoldenCoupledResearch.free right s = Rule30CriticalChargeOneCoreResearch.stream s := Rule30CriticalChargeOneCoreResearch.free_stream s

theorem psi_left : Rule30PeriodTwoSideways.Psi right = Rule30CriticalChargeOneCoreResearch.left := Rule30CriticalChargeOneCoreResearch.psi_left

theorem coupled_scale_counts (k : Nat) :
    zeros (Rule30GoldenCoupledResearch.free right) (14*k) = 7*k ∧
      blackCount (Rule30PeriodTwoSideways.Psi right) (2*(14*k)+1) = 12*k := by
  have h := Rule30CriticalChargeOneCoreResearch.coupled_scale_counts k
  constructor
  · rw [zeros_definition]; exact h.1
  · rw [blackCount_definition]; exact h.2

theorem unit_critical_charge_false (B : Nat) : ¬ CriticalCharge 1 B right := by
  intro hc
  exact Rule30CriticalChargeOneCoreResearch.unit_critical_charge_false B ((charge_definition 1 B right).mp hc)

theorem minimum_integer_coefficient {C B : Nat} (hc : CriticalCharge C B right) : 2≤C :=
  Rule30CriticalChargeOneCoreResearch.minimum_integer_coefficient ((charge_definition C B right).mp hc)

end Rule30CriticalChargeOneBridgeResearch
