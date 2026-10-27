module

public import Ruliology.CellularAutomata.Rule30TraceAmbiguity
public import Ruliology.CellularAutomata.Rule30Prize

/-!
Exact full first and second images of the two finite cutoff examples.
The cutoff includes physical site N. For N >= 2 each second image is the
fixed three-black row {-5,-4,-1} plus one explicit isolated right black.
The all-horizon corollary is finite-prefix ambiguity, not full trace equality.
-/

@[expose] public section
namespace Rule30CutoffImagesResearch

open Ruliology.CellularAutomata Rule30Jen Rule30Realization
open Rule30PeriodTwoSideways Rule30TraceEdge Rule30TraceMerge Rule30TraceAmbiguity

def leftLast (N : Nat) : Int := (N : Int) - ((N : Int) + 1) % 3
def rightLast (N : Nat) : Int := (N : Int) - ((N : Int) + 2) % 3

def cappedCommon (K p : Int) : Bool := if p <= K then commonImage p else false
def withIsolated (r p : Int) : Bool := finiteImage p || decide (p = r)

def PrimitiveFront100 (x : Int → Bool) (k : Int) : Prop :=
  x k = true ∧ x (k-1) = false ∧ x (k-2) = false ∧
    ∀ p, k < p → x p = false

theorem last_bounds (N : Nat) (hN : 2 ≤ N) :
    2 ≤ leftLast N ∧ leftLast N ≤ N ∧ leftLast N % 3 = 2 ∧
    1 ≤ rightLast N ∧ rightLast N ≤ N ∧ rightLast N % 3 = 1 := by
  unfold leftLast rightLast
  omega

theorem last_sites_mod_zero (N : Nat) (h : N % 3 = 0) :
    leftLast N = (N : Int)-1 ∧ rightLast N = (N : Int)-2 := by
  unfold leftLast rightLast
  omega

theorem last_sites_mod_one (N : Nat) (h : N % 3 = 1) :
    leftLast N = (N : Int)-2 ∧ rightLast N = (N : Int) := by
  unfold leftLast rightLast
  omega

theorem last_sites_mod_two (N : Nat) (h : N % 3 = 2) :
    leftLast N = (N : Int) ∧ rightLast N = (N : Int)-1 := by
  unfold leftLast rightLast
  omega

theorem left_last_values {k : Int} (hk : 2 ≤ k) (hm : k % 3 = 2) :
    leftExample k = true ∧ leftExample (k-1) = false ∧ leftExample (k-2) = false := by
  have h0 : ¬ k ≤ 0 := by omega
  have h1 : ¬ k-1 ≤ 0 := by omega
  have hm1 : (k-1)%3 ≠ 2 := by omega
  have hm2 : (k-2)%3 ≠ 2 := by omega
  refine ⟨by simp [leftExample,h0,hm],by simp [leftExample,h1,hm1],?_⟩
  by_cases h2 : k-2 ≤ 0
  · simp [leftExample,h2,show k-2 ≠ -3 by omega,show k-2 ≠ -1 by omega]
  · simp [leftExample,h2,hm2]

theorem right_last_values {k : Int} (hk : 1 ≤ k) (hm : k % 3 = 1) :
    rightExample k = true ∧ rightExample (k-1) = false ∧ rightExample (k-2) = false := by
  have h0 : ¬ k ≤ 0 := by omega
  have hm1 : (k-1)%3 ≠ 1 := by omega
  have hm2 : (k-2)%3 ≠ 1 := by omega
  refine ⟨by simp [rightExample,h0,hm],?_,?_⟩
  · by_cases h1 : k-1 ≤ 0
    · simp [rightExample,h1,show k-1 ≠ -3 by omega,show k-1 ≠ -2 by omega]
    · simp [rightExample,h1,hm1]
  · by_cases h2 : k-2 ≤ 0
    · simp [rightExample,h2,show k-2 ≠ -3 by omega,show k-2 ≠ -2 by omega]
    · simp [rightExample,h2,hm2]

theorem left_tail_white (N : Nat) (hN : 2 ≤ N) (p : Int)
    (hp : leftLast N < p) (hupper : p ≤ N) : leftExample p = false := by
  have hb := last_bounds N hN
  have hpos : ¬ p ≤ 0 := by omega
  have hm : p % 3 ≠ 2 := by unfold leftLast at hp; omega
  simp [leftExample,hpos,hm]

theorem right_tail_white (N : Nat) (hN : 2 ≤ N) (p : Int)
    (hp : rightLast N < p) (hupper : p ≤ N) : rightExample p = false := by
  have hb := last_bounds N hN
  have hpos : ¬ p ≤ 0 := by omega
  have hm : p % 3 ≠ 1 := by unfold rightLast at hp; omega
  simp [rightExample,hpos,hm]

theorem cutoff_above_last {x : Int → Bool} {N : Nat} {k : Int}
    (htail : ∀ p, k < p → p ≤ N → x p = false) {p : Int} (hp : k < p) :
    cutoff N x p = false := by
  by_cases h : p ≤ (N : Int)
  · simp [cutoff,h,htail p hp h]
  · simp [cutoff,h]

theorem cutoff_first_image {x : Int → Bool} {N : Nat} {k : Int}
    (hk : 1 ≤ k) (hkN : k ≤ N)
    (himage : ∀ p, evol x 1 p = commonImage p)
    (hblack : x k = true) (hwhite : x (k-1) = false)
    (htail : ∀ p, k < p → p ≤ N → x p = false) :
    evol (cutoff N x) 1 = cappedCommon (k+1) := by
  funext p
  by_cases hp : p < k
  · have h0 : p-1 ≤ (N : Int) := by omega
    have h1 : p ≤ (N : Int) := by omega
    have h2 : p+1 ≤ (N : Int) := by omega
    change rule (cutoff N x (p-1)) (cutoff N x p) (cutoff N x (p+1)) = _
    simp only [cutoff,ite_eq_left h0,ite_eq_left h1,ite_eq_left h2]
    change evol x 1 p = _
    rw [himage]
    simp [cappedCommon,show p ≤ k+1 by omega]
  · by_cases he : p = k
    · subst p
      have hz := cutoff_above_last htail (p:=k+1) (by omega)
      change rule (cutoff N x (k-1)) (cutoff N x k) (cutoff N x (k+1)) = _
      rw [hz]
      simp [cutoff,show k-1 ≤ (N : Int) by omega,hkN,hblack,hwhite,
        rule,cappedCommon,commonImage,show -4 ≤ k by omega,show k ≠ -2 by omega,
        show k ≤ k+1 by omega]
    · by_cases he1 : p = k+1
      · subst p
        have hz := cutoff_above_last htail (p:=k+1) (by omega)
        have hz2 := cutoff_above_last htail (p:=k+1+1) (by omega)
        change rule (cutoff N x (k+1-1)) (cutoff N x (k+1))
          (cutoff N x (k+1+1)) = _
        rw [show k+1-1=k by omega,hz,hz2]
        simp [cutoff,hkN,hblack,rule,cappedCommon,commonImage,
          show -4 ≤ k+1 by omega,show k+1 ≠ -2 by omega]
      · have h0 := cutoff_above_last htail (p:=p-1) (by omega)
        have h1 := cutoff_above_last htail (p:=p) (by omega)
        have h2 := cutoff_above_last htail (p:=p+1) (by omega)
        change rule (cutoff N x (p-1)) (cutoff N x p) (cutoff N x (p+1)) = _
        rw [h0,h1,h2]
        simp [rule,cappedCommon,show ¬ p ≤ k+1 by omega]

theorem capped_second_image (K : Int) (hK : 2 ≤ K) :
    evol (cappedCommon K) 1 = withIsolated (K+1) := by
  funext p
  by_cases hp : p < K
  · change rule (cappedCommon K (p-1)) (cappedCommon K p)
      (cappedCommon K (p+1)) = _
    simp only [cappedCommon,ite_eq_left (show p-1 ≤ K by omega),
      ite_eq_left (show p ≤ K by omega),ite_eq_left (show p+1 ≤ K by omega)]
    change evol commonImage 1 p = _
    rw [common_second_image]
    simp [withIsolated,show p ≠ K+1 by omega]
  · by_cases he : p = K
    · subst p
      simp [evol,cappedCommon,commonImage,finiteImage,withIsolated,rule,
        show K-1 ≤ K by omega,show -4 ≤ K-1 by omega,show -4 ≤ K by omega,
        show K-1 ≠ -2 by omega,show K ≠ -2 by omega,
        show ¬ K+1 ≤ K by omega,show K ≠ -5 by omega,
        show K ≠ -4 by omega,show K ≠ -1 by omega,show K ≠ K+1 by omega]
    · by_cases he1 : p = K+1
      · subst p
        simp [evol,cappedCommon,commonImage,finiteImage,withIsolated,rule,
          show K+1-1=K by omega,show -4 ≤ K by omega,show K ≠ -2 by omega,
          show ¬ K+1 ≤ K by omega,show ¬ K+1+1 ≤ K by omega]
      · have h0 : ¬ p-1 ≤ K := by omega
        have h1 : ¬ p ≤ K := by omega
        have h2 : ¬ p+1 ≤ K := by omega
        simp [evol,cappedCommon,h0,h1,h2,rule,withIsolated,finiteImage,he1,
          show p ≠ -5 by omega,show p ≠ -4 by omega,show p ≠ -1 by omega]

theorem cutoff_first_images (N : Nat) (hN : 2 ≤ N) :
    evol (cutoff N leftExample) 1 = cappedCommon (leftLast N+1) ∧
    evol (cutoff N rightExample) 1 = cappedCommon (rightLast N+1) := by
  obtain ⟨hl,hlN,hlm,hr,hrN,hrm⟩ := last_bounds N hN
  have hleft := left_last_values hl hlm
  have hright := right_last_values hr hrm
  exact ⟨cutoff_first_image (by omega) hlN (fun p => (one_step_images p).1)
      hleft.1 hleft.2.1 (left_tail_white N hN),
    cutoff_first_image hr hrN (fun p => (one_step_images p).2)
      hright.1 hright.2.1 (right_tail_white N hN)⟩

theorem cutoff_second_images (N : Nat) (hN : 2 ≤ N) :
    evol (cutoff N leftExample) 2 = withIsolated (leftLast N+2) ∧
    evol (cutoff N rightExample) 2 = withIsolated (rightLast N+2) := by
  have hf := cutoff_first_images N hN
  have hb := last_bounds N hN
  constructor
  · rw [show 2=1+1 from rfl,← restart_row,hf.1,capped_second_image _ (by omega)]
    rw [show leftLast N+1+1=leftLast N+2 by omega]
  · rw [show 2=1+1 from rfl,← restart_row,hf.2,capped_second_image _ (by omega)]
    rw [show rightLast N+1+1=rightLast N+2 by omega]

theorem cutoff_fronts (N : Nat) (hN : 2 ≤ N) :
    PrimitiveFront100 (cutoff N leftExample) (leftLast N) ∧
    PrimitiveFront100 (cutoff N rightExample) (rightLast N) := by
  obtain ⟨hl,hlN,hlm,hr,hrN,hrm⟩ := last_bounds N hN
  have hleft := left_last_values hl hlm
  have hright := right_last_values hr hrm
  constructor
  · refine ⟨?_,?_,?_,fun p hp => cutoff_above_last (left_tail_white N hN) hp⟩
    · simpa [cutoff,hlN] using hleft.1
    · simpa [cutoff,show leftLast N-1 ≤ (N : Int) by omega] using hleft.2.1
    · simpa [cutoff,show leftLast N-2 ≤ (N : Int) by omega] using hleft.2.2
  · refine ⟨?_,?_,?_,fun p hp => cutoff_above_last (right_tail_white N hN) hp⟩
    · simpa [cutoff,hrN] using hright.1
    · simpa [cutoff,show rightLast N-1 ≤ (N : Int) by omega] using hright.2.1
    · simpa [cutoff,show rightLast N-2 ≤ (N : Int) by omega] using hright.2.2

theorem arbitrarily_long_primitive_finite_ambiguity (H : Nat) :
    ∃ (x y : Int → Bool) (r s : Int), FinConfig x ∧ FinConfig y ∧
      HasLeftEdge x (-3) ∧ HasLeftEdge y (-3) ∧ x (-1) ≠ y (-1) ∧
      PrimitiveFront100 x r ∧ PrimitiveFront100 y s ∧
      (∀ t, t < H → evol x t 0 = evol y t 0) := by
  let N := max 2 H
  have hN : 2 ≤ N := Nat.le_max_left _ _
  have hf := cutoff_fronts N hN
  refine ⟨cutoff N leftExample,cutoff N rightExample,leftLast N,rightLast N,
    cutoff_finite (fun _ h => left_white h) N,
    cutoff_finite (fun _ h => right_white h) N,
    cutoff_edge left_edge N,cutoff_edge right_edge N,?_,hf.1,hf.2,?_⟩
  · simpa [cutoff] using different_left_neighbor
  · intro t ht
    have hH : H ≤ N := Nat.le_max_right _ _
    rw [cutoff_trace _ _ _ (by omega),cutoff_trace _ _ _ (by omega)]
    exact same_center_trace t

theorem isolated_images_finite_agreement (N t : Nat) (hN : 2 ≤ N) (ht : t+2 ≤ N) :
    evol (withIsolated (leftLast N+2)) t 0 =
      evol (withIsolated (rightLast N+2)) t 0 := by
  have hi := cutoff_second_images N hN
  rw [← hi.1,← hi.2,Rule30ZeroBoundaryBarriers.evol_restart,
    Rule30ZeroBoundaryBarriers.evol_restart]
  rw [cutoff_trace _ _ _ (by omega),cutoff_trace _ _ _ (by omega)]
  exact same_center_trace (2+t)

end Rule30CutoffImagesResearch
