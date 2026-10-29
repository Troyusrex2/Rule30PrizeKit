module
public import Ruliology.CellularAutomata.Rule30UniversalStart
public import Ruliology.CellularAutomata.Rule30ProfileClockSharpness

/-! Combined corollary of ghywel's PR54 and the ranked escape in PR55.
This formulation transports the period assertion extensionally, avoiding
normalization of the noncomputable chosen prefix exponent. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30UniversalStartEscape
open Rule30RightProfiles Rule30RightPrefixClock Rule30ProfileClockEscape
open Rule30ProfileClockSharpness
set_option maxRecDepth 30000
set_option maxHeartbeats 20000000

def FirstDefect (x : Int → Bool) (m : Nat) : Prop :=
  2≤m ∧ x (-(m:Int))=x (-((m:Int)-1)) ∧
    ∀d:Nat,2≤d → d<m → x (-(d:Int))≠x (-((d:Int)-1))

theorem first_defect_nonperiod_two (x : Int → Bool) (h0 : x 0=true)
    (hr : ∀i:Int,0<i → x i=false) (m : Nat) (hm : FirstDefect x m) :
    ¬Period (rightDiag x ((m+1:Nat):Int)) 2 := by
  have least := (Rule30UniversalStart.universal_start x h0 hr m hm.1 hm.2.1 hm.2.2).1
  intro per
  exact least.2 2 (by omega) (by omega) per

theorem escape_fifteen (x : Int → Bool) (hr : ∀i:Int,0<i → x i=false)
    (m : Nat) (bad : ¬Period (rightDiag x ((m+1:Nat):Int)) 2) :
    ¬PrefixPer (rightDiag x) ((m:Int)+15) 32 := by
  intro small
  have bad0 : ¬Period (rightDiag x (-(0:Int)+((m+1:Nat):Int))) 2 := by
    simpa only [Int.neg_zero,Int.zero_add] using bad
  apply no_period32_extension x 0 hr (m+1) bad0
  intro i hi
  exact small i (by omega)

theorem first_defect_no_prefix32 (x : Int → Bool) (h0 : x 0=true)
    (hr : ∀i:Int,0<i → x i=false) (m : Nat) (hm : FirstDefect x m) :
    ¬PrefixPer (rightDiag x) ((m:Int)+15) 32 :=
  escape_fifteen x hr m (first_defect_nonperiod_two x h0 hr m hm)

theorem finite_seed_no_prefix32 (x : Int → Bool) (h0 : x 0=true)
    (hr : ∀i:Int,0<i → x i=false) (L : Nat)
    (hl : ∀i:Int,i< -(L:Int) → x i=false) :
    ∃m:Nat,2≤m ∧ ¬PrefixPer (rightDiag x) ((m:Int)+15) 32 := by
  obtain ⟨m,hm,least,_⟩ := Rule30UniversalStart.universal_start_finite x h0 hr L hl
  refine ⟨m,hm,escape_fifteen x hr m ?_⟩
  intro per
  exact least.2 2 (by omega) (by omega) per

theorem witness_first_defect : FirstDefect (wordSeed 47649) 2 := by
  refine ⟨by omega,by decide +kernel,?_⟩
  intro d hd htop
  omega

theorem sharp_fifteen_witness :
    FirstDefect (wordSeed 47649) 2 ∧
    PrefixPer (rightDiag (wordSeed 47649)) 16 32 ∧
    ¬PrefixPer (rightDiag (wordSeed 47649)) 17 32 :=
  ⟨witness_first_defect,witness_prefix32,
    first_defect_no_prefix32 _ (by decide +kernel) (seed_right 47649) 2 witness_first_defect⟩

theorem fourteen_after_defect_is_not_uniform :
    ¬(∀x:Int → Bool,x 0=true → (∀i:Int,0<i → x i=false) →
      ∀m:Nat,FirstDefect x m → ¬PrefixPer (rightDiag x) ((m:Int)+14) 32) := by
  intro uniform
  exact uniform (wordSeed 47649) (by decide +kernel) (seed_right 47649) 2
    witness_first_defect witness_prefix32

end Ruliology.CellularAutomata.Rule30UniversalStartEscape
