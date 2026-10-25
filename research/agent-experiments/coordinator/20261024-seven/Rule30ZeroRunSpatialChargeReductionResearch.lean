import Rule30TotalSpatialChargeReductionResearch

/-! An optional stronger target removes the no-adjacent-zero premise by
counting starts of zero runs. The proposed spatial inequality is unproved. -/

namespace Rule30ZeroRunSpatialChargeReductionResearch
open Ruliology.CellularAutomata
open Rule30CoupledChargeReductionResearch (zeros)
open Rule30TotalSpatialChargeReductionResearch (blackCount No00SpatialCharge)

def zeroRuns (s : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => zeroRuns s n +
      if s n then 0 else if n=0 then 1 else if s (n-1) then 1 else 0

theorem zeroRuns_eq_zeros_of_no00 {s : Nat → Bool}
    (h : ∀ k, s k=false → s (k+1)=true) (n : Nat) : zeroRuns s n=zeros s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zeroRuns,zeros,ih]
    cases hs : s n with
    | true => simp [hs]
    | false =>
      cases n with
      | zero => simp [hs]
      | succ n =>
        have hp : s n=true := by
          cases hp : s n with
          | true => rfl
          | false =>
            have hc := h n hp
            rw [hs] at hc
            cases hc
        simp [hs,hp]

def ZeroRunSpatialCharge : Prop := ∀ (s : Nat → Bool) n,
  zeroRuns s n ≤ blackCount (Rule30ZeroBoundary.Theta s) (2*n+1)

theorem no00_charge_of_zero_run_charge (hc : ZeroRunSpatialCharge) : No00SpatialCharge := by
  intro s hs n
  rw [←zeroRuns_eq_zeros_of_no00 hs n]
  exact hc s n

theorem CQ01_of_zero_run_spatial_charge (hc : ZeroRunSpatialCharge) :
    Rule30PeriodTwoCoupled.CQ01 :=
  Rule30TotalSpatialChargeReductionResearch.CQ01_of_no00_spatial_charge
    (no00_charge_of_zero_run_charge hc)

end Rule30ZeroRunSpatialChargeReductionResearch
