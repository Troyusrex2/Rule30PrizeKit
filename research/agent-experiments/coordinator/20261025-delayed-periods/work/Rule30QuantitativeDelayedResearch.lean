import Rule30DelayedPeriodsResearch

namespace Rule30QuantitativeDelayedResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30StripCertificates Rule30TailClassesResearch
open Rule30DelayedDefectResearch Rule30DelayedPeriodsResearch

theorem collision_of_periodic_prefix (rows : Nat → Nat → Bool) (P : Nat) (hP : 0<P)
    (hp : ∀ j, j≤2^P → SpatialPeriod P (rows j)) :
    ∃ m n, m<n ∧ n≤2^P ∧ TailEq (rows m) (rows n) := by
  classical
  let threshold (j : Nat) := if hj : j≤2^P then Classical.choose (hp j hj) else 0
  have hthreshold (j : Nat) (hj : j≤2^P) :
      ∀ d, threshold j≤d → rows j (d+P)=rows j d := by
    simpa only [threshold,dite_eq_left hj] using Classical.choose_spec (hp j hj)
  obtain ⟨D,hD⟩ := finite_bound threshold (2^P)
  let window (j : Nat) := seg (fun i => rows j (D+i)) P
  obtain ⟨m,n,hmn,hn,hwin⟩ := Rule30Jen.pigeonhole P window
    (fun j => length_seg P _)
  refine ⟨m,n,hmn,hn,agree_from_window _ _ D P hP ?_ ?_ hwin⟩
  · intro d hd
    apply hthreshold m (by omega) d
    have := hD m (by omega)
    omega
  · intro d hd
    apply hthreshold n hn d
    have := hD n hn
    omega

theorem spatial_period_time {a : Nat → Bool} {P : Nat}
    (h : SpatialPeriod P (fun d => recon a d 0)) (t : Nat) :
    SpatialPeriod P (fun d => recon a d t) := by
  obtain ⟨D,hD⟩ := h
  refine ⟨D+1+t,fun d hd => ?_⟩
  have ht := zrow_translate (L:=lam a) (L':=lam a) (d:=P) (a:=D+1)
    (by omega) (fun k hk => hD k (by omega)) t d hd
  simpa only [zrow_lam] using ht

theorem input_shift_index (i j : Nat) (hij : i≤j) :
    (fun t => input j (t+8*(j-i)))=input i := by
  funext t
  have he : t+8*(j-i)=8*j+5 ↔ t=8*i+5 := by omega
  have hm : (t+8*(j-i))%4=t%4 := by omega
  simp only [input,Rule30DelayedDefectResearch.pure,he,hm]

theorem period_inherited {P i j : Nat} (hij : i≤j)
    (h : SpatialPeriod P (fun d => recon (input j) d 0)) :
    SpatialPeriod P (fun d => recon (input i) d 0) := by
  have ht := spatial_period_time h (8*(j-i))
  have he : (fun d => recon (input j) d (8*(j-i)))=
      (fun d => recon (input i) d 0) := by
    funext d
    simpa only [Nat.zero_add,input_shift_index i j hij] using
      recon_shift (input j) (8*(j-i)) d 0
  simpa only [he] using ht

/-- A row with eventual spatial period P cannot hide a defect delayed by
2^P or more family steps, regardless of its spatial transient. -/
theorem delay_lt_pow_period (j P : Nat) (hP : 0<P)
    (h : SpatialPeriod P (fun d => recon (input j) d 0)) : j<2^P := by
  apply Nat.lt_of_not_ge
  intro hj
  have hp : ∀ i, i≤2^P → SpatialPeriod P (fun d => recon (input i) d 0) := by
    intro i hi
    exact period_inherited (by omega) h
  obtain ⟨m,n,hmn,hn,he⟩ := collision_of_periodic_prefix _ P hP hp
  exact pairwise_tail_distinct m n hmn he

theorem pow_two_mono {p q : Nat} (h : p≤q) : 2^p≤2^q := by
  obtain ⟨r,rfl⟩ : ∃ r, q=p+r := ⟨q-p,by omega⟩
  induction r with
  | zero => exact Nat.le_refl _
  | succ r ih =>
    rw [show p+(r+1)=(p+r)+1 by omega,Nat.pow_succ]
    omega

/-- An explicit witness for every desired lower bound: put the one
white-to-black temporal defect at time 8*2^M+5. -/
theorem explicit_large_periods (M : Nat) :
    Rule30Jen.EventuallyPeriodic (fun d => recon (input (2^M)) d 0) ∧
    ∀ P, 0<P → P≤M → ¬SpatialPeriod P (fun d => recon (input (2^M)) d 0) := by
  refine ⟨family_spatial_periodic _,fun P hP hM hper => ?_⟩
  have hlt := delay_lt_pow_period (2^M) P hP hper
  have hle := pow_two_mono hM
  omega

theorem input_eq_alt (j : Nat) : input j=alt (free j) := by
  funext t
  obtain ⟨s,rfl|rfl⟩ : ∃ s, t=2*s ∨ t=2*s+1 := ⟨t/2,by omega⟩
  · rw [input_even]
    simp [alt]
  · simp [alt,free,show (2*s+1)/2=s by omega]

theorem theta_eq_recon (j : Nat) : Theta (free j)=(fun d => recon (input j) d 0) := by
  funext d
  unfold Theta lam
  rw [←input_eq_alt]

theorem theta_inX (j : Nat) : InX (Theta (free j)) := Theta_inX _

theorem theta_spatial_periodic (j : Nat) : Rule30Jen.EventuallyPeriodic (Theta (free j)) := by
  rw [theta_eq_recon]
  exact family_spatial_periodic j

theorem theta_delay_lt_pow_period (j P : Nat) (hP : 0<P)
    (h : SpatialPeriod P (Theta (free j))) : j<2^P := by
  rw [theta_eq_recon] at h
  exact delay_lt_pow_period j P hP h

theorem theta_explicit_large_periods (M : Nat) :
    Rule30Jen.EventuallyPeriodic (Theta (free (2^M))) ∧
    ∀ P, 0<P → P≤M → ¬SpatialPeriod P (Theta (free (2^M))) := by
  rw [theta_eq_recon]
  exact explicit_large_periods M

end Rule30QuantitativeDelayedResearch
