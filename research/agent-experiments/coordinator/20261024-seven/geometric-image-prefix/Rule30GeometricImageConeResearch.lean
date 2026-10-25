import Ruliology.CellularAutomata.Rule30Prize
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! A polynomial cone certificate, uniform for every integer scale >=1.
The two cone generators arise from actual finite-image tail pumps. -/
namespace Rule30GeometricImageConeResearch

def whiteB (x : Int) : Int := x^3-x+1
def whiteA (x : Int) : Int := x^5-x^3+x-1
def whiteCharge (x c0 c1 : Int) : Int := whiteB x*c0+whiteA x*c1
def blackCharge (x c0 c1 : Int) : Int := (x-1)*c0+whiteB x*c1
def delta0 (x : Int) : Int := x^9+x^4+x^3-x^5-1
def delta1 (x : Int) : Int := x^11+x^10+x^8+x^5-x^4-x^3+1
def delta (x c0 c1 : Int) : Int := delta0 x*c0+delta1 x*c1
def determinant (x : Int) : Int := x^3*(x^2-x+1)
def alphaWeight (x : Int) : Int := x^7+x^6-x^3
def betaWeight (x : Int) : Int := x^13+x^11+x^10-x^9+x^5

theorem cone_identity (x c0 c1 : Int) :
    determinant x*delta x c0 c1=
      alphaWeight x*whiteCharge x c0 c1+betaWeight x*blackCharge x c0 c1 := by
  unfold determinant delta delta0 delta1 alphaWeight betaWeight whiteCharge blackCharge whiteA whiteB
  ring

theorem determinant_positive {x : Int} (hx : 1≤x) : 0<determinant x := by
  have hpos : 0<x := by omega
  have hsub : 0≤x-1 := by omega
  have he : determinant x=x^3*((x-1)^2+(x-1)+1) := by unfold determinant;ring
  rw [he]
  positivity

theorem alpha_nonnegative {x : Int} (hx : 1≤x) : 0≤alphaWeight x := by
  have hpos : 0<x := by omega
  have hsub : 0≤x-1 := by omega
  have he : alphaWeight x=x^3*((x-1)*(x^3+x^2+x+1)+x^3) := by unfold alphaWeight;ring
  rw [he]
  positivity

theorem beta_nonnegative {x : Int} (hx : 1≤x) : 0≤betaWeight x := by
  have hpos : 0<x := by omega
  have hsub : 0≤x-1 := by omega
  have he : betaWeight x=x^9*((x-1)*(x^3+x^2+x+1)+x^2+x)+x^5 := by unfold betaWeight;ring
  rw [he]
  positivity

theorem delta_nonnegative {x : Int} (hx : 1≤x) (c0 c1 : Int)
    (hw : 0≤whiteCharge x c0 c1) (hb : 0≤blackCharge x c0 c1) :
    0≤delta x c0 c1 := by
  have hprod:=Int.add_nonneg (Int.mul_nonneg (alpha_nonnegative hx) hw)
    (Int.mul_nonneg (beta_nonnegative hx) hb)
  rw [←cone_identity] at hprod
  have hdet:=determinant_positive hx
  apply Classical.byContradiction
  intro hn
  have hneg : delta x c0 c1<0 := by omega
  have h:=Int.mul_lt_mul_of_pos_left hneg hdet
  simp only [Int.mul_zero] at h
  omega

end Rule30GeometricImageConeResearch
