import Rule30GoldenQuantitativeDriftResearch

/-! A sufficient charge target with subunit slack per dyadic scale.
For EACH base m, the constants C and B may be chosen separately. This
quantifier order matters: shared constants for all m would recover a
pointwise critical bound already by setting k=1 and varying m.
No scale charge is asserted here; the premise remains unproved.
-/
namespace Rule30GoldenScaleChargeResearch
open Ruliology.CellularAutomata
open Rule30GoldenQuantitativeDriftResearch (cutoff defects_at_cutoff)
open Rule30GoldenCriticalDriftResearch (CriticalCharge count_identity trailing_le_four)
open Rule30TotalSpatialChargeReductionResearch (blackCount blackCount_le_cutoff)
open Rule30CoupledChargeReductionResearch (zeros)

def ScaleCharge (C B : Nat) (R : Nat -> Bool) (m : Nat) : Prop := forall k,
  5*zeros (Rule30GoldenCoupledResearch.free R) (cutoff m k) <=
    cutoff m k+B+C*blackCount (Rule30PeriodTwoSideways.Psi R) (2*cutoff m k+1)+k/2

def ScaleCharges (R : Nat -> Bool) : Prop := forall m, exists C B, ScaleCharge C B R m

theorem scale_charges_of_critical_charge {C B : Nat} {R : Nat -> Bool}
    (hc : CriticalCharge C B R) : ScaleCharges R := by
  intro m
  refine ⟨C,B,?_⟩
  intro k
  have h := hc (cutoff m k)
  omega

theorem not_finSupp_psi_of_scale_charges {R : Nat -> Bool}
    (hc : ScaleCharges R) :
    Not (Rule30ZeroBoundary.FinSupp (Rule30PeriodTwoSideways.Psi R)) := by
  rintro ⟨W,hW⟩
  have hX := Rule30PeriodTwoSideways.Psi_inX R
  obtain ⟨m,hm,hedge,hzero⟩ := Rule30ZeroBoundary.last_black
    (L:=Rule30PeriodTwoSideways.Psi R)
    (show Rule30PeriodTwoSideways.Psi R 1=true from hX 0) W hW
  obtain ⟨C,B,hCB⟩ := hc m
  let k := 2*(B+C*(m+1)+5)
  have hd := defects_at_cutoff hm hedge hzero hX (Rule30GoldenCoupledResearch.golden_free R) k
  have hi := count_identity (Rule30GoldenCoupledResearch.golden_free R) (cutoff m k)
  have ht := trailing_le_four (Rule30GoldenCoupledResearch.golden_free R) (cutoff m k)
  have hb := blackCount_le_cutoff (L:=Rule30PeriodTwoSideways.Psi R) (W:=m+1)
    (fun d hd => hzero d (by omega)) (2*cutoff m k+1)
  have hmul := Nat.mul_le_mul_left C hb
  have hcharge := hCB k
  change k<=Rule30GoldenCriticalDriftResearch.defects (Rule30GoldenCoupledResearch.free R) (cutoff m k) at hd
  have hbad : k<=B+C*(m+1)+k/2+4 := by omega
  dsimp only [k] at hbad
  omega

theorem CQ01_of_scale_charges
    (hc : forall R, Rule30ZeroBoundary.FinSupp R -> ScaleCharges R) :
    Rule30PeriodTwoCoupled.CQ01 := by
  apply Rule30PeriodTwoSideways.CQ01_iff_Psi.mpr
  intro R hR
  exact not_finSupp_psi_of_scale_charges (hc R hR)

end Rule30GoldenScaleChargeResearch
