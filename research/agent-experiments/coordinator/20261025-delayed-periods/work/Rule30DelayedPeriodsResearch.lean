import Rule30DelayedDefectResearch
import Rule30PeriodicReconstructionResearch

namespace Rule30DelayedPeriodsResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30TailClassesResearch
open Rule30DelayedDefectResearch Rule30PeriodicReconstructionResearch

def commonMul : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*commonMul n

theorem commonMul_pos (n : Nat) : 0<commonMul n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem dvd_commonMul (p n : Nat) (hp : 0<p) (hn : p≤n) : p∣commonMul n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : p=n+1
    · exact ⟨commonMul n,by simp [commonMul,he]⟩
    · obtain ⟨q,hq⟩ := ih (by omega)
      refine ⟨(n+1)*q,?_⟩
      simp [commonMul,hq,Nat.mul_left_comm]

theorem spatial_period_multiple {f : Nat → Bool} {P Q : Nat}
    (h : SpatialPeriod P f) (hq : P∣Q) : SpatialPeriod Q f := by
  obtain ⟨D,hD⟩ := h
  obtain ⟨q,rfl⟩ := hq
  exact ⟨D,fun d hd => by simpa [Nat.mul_comm] using Rule30Jen.periodic_mul hD q d hd⟩

theorem input_tail (j t : Nat) (ht : 8*j+8≤t) : input j t=pure t := by
  simp [input,show t≠8*j+5 by omega]

theorem input_time_period (j t : Nat) (ht : 8*j+8≤t) : input j (t+4)=input j t := by
  rw [input_tail j (t+4) (by omega),input_tail j t ht]
  have hm : (t+4)%4=t%4 := by omega
  simp [Rule30DelayedDefectResearch.pure,hm]

theorem family_spatial_periodic (j : Nat) :
    Rule30Jen.EventuallyPeriodic (fun d => recon (input j) d 0) :=
  spatial_of_temporal _ (8*j+8) 4 (by decide) (input_time_period j)

theorem no_uniform_period_bound (M : Nat) :
    ¬∀ j, ∃ P, 0<P ∧ P≤M ∧ SpatialPeriod P (fun d => recon (input j) d 0) := by
  intro h
  apply no_common_spatial_period (commonMul M) (commonMul_pos M)
  intro j
  obtain ⟨P,hP,hM,hper⟩ := h j
  exact spatial_period_multiple hper (dvd_commonMul P M hP hM)

/-- Every delayed-defect row is eventually spatially periodic, but their
least possible eventual periods exceed every uniform finite bound. -/
theorem arbitrarily_large_periods (M : Nat) :
    ∃ j, Rule30Jen.EventuallyPeriodic (fun d => recon (input j) d 0) ∧
      ∀ P, 0<P → P≤M → ¬SpatialPeriod P (fun d => recon (input j) d 0) := by
  classical
  have hex : ∃ j, ¬∃ P, 0<P ∧ P≤M ∧ SpatialPeriod P (fun d => recon (input j) d 0) := by
    apply Classical.byContradiction
    intro h
    apply no_uniform_period_bound M
    intro j
    apply Classical.byContradiction
    intro hp
    exact h ⟨j,hp⟩
  obtain ⟨j,hj⟩ := hex
  exact ⟨j,family_spatial_periodic j,fun P hp hM hper => hj ⟨P,hp,hM,hper⟩⟩

def free (j s : Nat) : Bool := input j (2*s+1)

theorem input_even (j s : Nat) : input j (2*s)=true := by
  have he : 2*s≠8*j+5 := by omega
  have hm : (2*s)%4≠1 := by omega
  simp [input,he,Rule30DelayedDefectResearch.pure,hm]

theorem free_formula (j s : Nat) :
    free j s=if s=4*j+2 then true else decide (s%2=1) := by
  have he : 2*s+1=8*j+5 ↔ s=4*j+2 := by omega
  have hm : (2*s+1)%4≠1 ↔ s%2=1 := by omega
  simp only [free,input,Rule30DelayedDefectResearch.pure,he,hm]

theorem free_true_iff (j s : Nat) : free j s=true ↔ s=4*j+2 ∨ s%2=1 := by
  by_cases hs : s=4*j+2 <;> simp [free_formula,hs]

theorem free_false_iff (j s : Nat) : free j s=false ↔ s≠4*j+2 ∧ s%2=0 := by
  by_cases hs : s=4*j+2
  · simp [free_formula,hs]
  · by_cases hm : s%2=1
    · simp [free_formula,hs,hm]
    · have hm0 : s%2=0 := by omega
      simp [free_formula,hs,hm0]

theorem free_no_double_zero (j s : Nat) (h : free j s=false) : free j (s+1)=true := by
  have h0 := (free_false_iff j s).mp h
  exact (free_true_iff j (s+1)).mpr (Or.inr (by omega))

theorem free_no_five_ones (j s : Nat) :
    ¬(free j s=true ∧ free j (s+1)=true ∧ free j (s+2)=true ∧
      free j (s+3)=true ∧ free j (s+4)=true) := by
  rintro ⟨h0,h1,h2,h3,h4⟩
  have h0' := (free_true_iff j s).mp h0
  have h1' := (free_true_iff j (s+1)).mp h1
  have h2' := (free_true_iff j (s+2)).mp h2
  have h3' := (free_true_iff j (s+3)).mp h3
  have h4' := (free_true_iff j (s+4)).mp h4
  omega

theorem free_no_010110 (j s : Nat) :
    ¬(free j s=false ∧ free j (s+1)=true ∧ free j (s+2)=false ∧
      free j (s+3)=true ∧ free j (s+4)=true ∧ free j (s+5)=false) := by
  rintro ⟨h0,h1,h2,h3,h4,h5⟩
  have h0' := (free_false_iff j s).mp h0
  have h5' := (free_false_iff j (s+5)).mp h5
  omega

theorem free_no_1011010 (j s : Nat) :
    ¬(free j s=true ∧ free j (s+1)=false ∧ free j (s+2)=true ∧
      free j (s+3)=true ∧ free j (s+4)=false ∧ free j (s+5)=true ∧ free j (s+6)=false) := by
  rintro ⟨h0,h1,h2,h3,h4,h5,h6⟩
  have h1' := (free_false_iff j (s+1)).mp h1
  have h4' := (free_false_iff j (s+4)).mp h4
  omega

end Rule30DelayedPeriodsResearch
