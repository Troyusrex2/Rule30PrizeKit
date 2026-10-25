import Rule30CoupledChargeReductionResearch

/-! A weaker counting target than the even-only charge: both spatial
parities count, and constants may depend on the right half. The counting
premise remains an explicit, unproved hypothesis. -/

namespace Rule30TotalSpatialChargeReductionResearch
open Ruliology.CellularAutomata
open Rule30CoupledChargeReductionResearch (zeros zeros_lower_bound)

def blackCount (L : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => blackCount L n + (L n).toNat

theorem blackCount_le_length (L : Nat → Bool) (n : Nat) : blackCount L n ≤ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hb : (L n).toNat ≤ 1 := by cases L n <;> decide
    rw [blackCount]
    omega

theorem blackCount_le_cutoff {L : Nat → Bool} {W : Nat}
    (hW : ∀ d, W ≤ d → L d = false) (K : Nat) : blackCount L K ≤ W := by
  induction K with
  | zero => exact Nat.zero_le _
  | succ K ih =>
    by_cases hk : K < W
    · have h := blackCount_le_length L K
      have hb : (L K).toNat ≤ 1 := by cases L K <;> decide
      rw [blackCount]
      omega
    · rw [blackCount, hW K (by omega)]
      simpa using ih

def SpatialCharge (C B : Nat) (R : Nat → Bool) : Prop := ∀ n,
  zeros (Rule30GoldenCoupledResearch.free R) n ≤
    B + C * blackCount (Rule30PeriodTwoSideways.Psi R) (2*n+1)

theorem not_finSupp_psi_of_spatial_charge {C B : Nat} {R : Nat → Bool}
    (hc : SpatialCharge C B R) :
    ¬ Rule30ZeroBoundary.FinSupp (Rule30PeriodTwoSideways.Psi R) := by
  rintro ⟨W,hW⟩
  have hb := blackCount_le_cutoff (W := W+1) (fun d hd => hW d (by omega))
    (2*(5*(B+C*(W+1)+1))+1)
  have hm := Nat.mul_le_mul_left C hb
  have hz := zeros_lower_bound (Rule30GoldenCoupledResearch.golden_free R) (B+C*(W+1)+1)
  have hcharge := hc (5*(B+C*(W+1)+1))
  omega

theorem CQ01_of_spatial_charge
    (hc : ∀ R, Rule30ZeroBoundary.FinSupp R → ∃ C B, SpatialCharge C B R) :
    Rule30PeriodTwoCoupled.CQ01 := by
  apply Rule30PeriodTwoSideways.CQ01_iff_Psi.mpr
  intro R hR
  obtain ⟨C,B,hCB⟩ := hc R hR
  exact not_finSupp_psi_of_spatial_charge hCB

/-- The stronger, constant-one target tested by the finite experiments.
It is not asserted here. No restriction on five consecutive ones is needed
in this premise. -/
def No00SpatialCharge : Prop := ∀ s : Nat → Bool,
  (∀ k, s k = false → s (k+1) = true) → ∀ n,
    zeros s n ≤ blackCount (Rule30ZeroBoundary.Theta s) (2*n+1)

theorem CQ01_of_no00_spatial_charge (hc : No00SpatialCharge) :
    Rule30PeriodTwoCoupled.CQ01 := by
  apply CQ01_of_spatial_charge
  intro R _
  refine ⟨1,0,?_⟩
  intro n
  have hfree : Rule30GoldenCoupledResearch.free R =
      (fun k => !Rule30PeriodTwoSideways.u R k) := by
    funext k
    exact Rule30PeriodTwoSideways.Psi_free R k
  have htheta : Rule30ZeroBoundary.Theta (Rule30GoldenCoupledResearch.free R) =
      Rule30PeriodTwoSideways.Psi R := by rw [hfree]; rfl
  have hb := hc _ (Rule30GoldenCoupledResearch.golden_free R).1 n
  rw [htheta] at hb
  simpa using hb

end Rule30TotalSpatialChargeReductionResearch
