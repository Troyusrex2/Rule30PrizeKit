import Rule30TotalSpatialChargeReductionResearch

/-! A critical-density reduction. The new counting inequality is an explicit
hypothesis. Bounded excess over the minimum Golden zero density forces
eventual period five, which is impossible for a finite constrained start. -/

namespace Rule30GoldenCriticalDriftResearch
open Ruliology.CellularAutomata
open Rule30GoldenDFAResearch (Golden)
open Rule30CoupledChargeReductionResearch (zeros)
open Rule30TotalSpatialChargeReductionResearch (blackCount blackCount_le_cutoff)

def trailing (s : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => if s n then trailing s n+1 else 0

theorem trailing_le (s : Nat → Bool) (n : Nat) : trailing s n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => cases hs : s n <;> simp [trailing,hs] <;> omega

theorem trailing_bit (s : Nat → Bool) (n i : Nat) (hi : i < trailing s n) :
    s (n-(i+1))=true := by
  induction n generalizing i with
  | zero => simp [trailing] at hi
  | succ n ih =>
    cases hs : s n with
    | false => simp [trailing,hs] at hi
    | true =>
      simp only [trailing,hs,↓reduceIte] at hi
      cases i with
      | zero => simpa using hs
      | succ i =>
        have h := ih i (by omega)
        have he : n+1-(i+1+1)=n-(i+1) := by omega
        simpa only [he] using h

theorem trailing_le_four {s : Nat → Bool} (hg : Golden s) (n : Nat) :
    trailing s n ≤ 4 := by
  apply Classical.byContradiction
  intro hn
  have hl := trailing_le s n
  have hb (i : Nat) (hi : i<5) : s (n-5+i)=true := by
    have h := trailing_bit s n (4-i) (by omega)
    have he : n-((4-i)+1)=n-5+i := by omega
    simpa only [he] using h
  exact hg.2 (n-5) ⟨by simpa using hb 0 (by omega),hb 1 (by omega),
    hb 2 (by omega),hb 3 (by omega),hb 4 (by omega)⟩

def defects (s : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => defects s n + if s n then 0 else 4-trailing s n

theorem count_identity {s : Nat → Bool} (hg : Golden s) (n : Nat) :
    5*zeros s n+trailing s n=n+defects s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hb := trailing_le_four hg n
    cases hs : s n <;> simp [zeros,trailing,defects,hs] <;> omega

theorem defects_mono (s : Nat → Bool) : ∀ {a b : Nat}, a≤b → defects s a≤defects s b := by
  intro a b hab
  induction b with
  | zero =>
    have ha : a=0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases h : a≤b
    · have hn : defects s b≤defects s (b+1) := by rw [defects]; omega
      exact Nat.le_trans (ih h) hn
    · have ha : a=b+1 := by omega
      subst a
      exact Nat.le_refl _

theorem monotone_bounded_constant (f : Nat → Nat) (hf : ∀ {a b : Nat}, a≤b → f a≤f b) (M : Nat) :
    (∀ n, f n≤M) → ∃ N, ∀ n, N≤n → f n=f N := by
  classical
  induction M with
  | zero =>
    intro hb
    refine ⟨0,fun n _ => ?_⟩
    have h0 := hb 0
    have hn := hb n
    omega
  | succ M ih =>
    intro hb
    by_cases he : ∃ n, f n=M+1
    · obtain ⟨N,hN⟩ := he
      refine ⟨N,fun n hn => ?_⟩
      have hmono := hf hn
      have hbound := hb n
      omega
    · apply ih
      intro n
      have hbound := hb n
      have hne : f n≠M+1 := fun h => he ⟨n,h⟩
      omega

theorem period_five_of_zero_predecessor {s : Nat → Bool} (hg : Golden s) (N : Nat)
    (hz : ∀ n, N≤n → s n=false → trailing s n=4) :
    ∀ n, N≤n → s (n+5)=s n := by
  intro n hn
  cases hs : s n with
  | false =>
    have hnext (j : Nat) (hj : 1≤j) (hj4 : j≤4) : s (n+j)=true := by
      cases hv : s (n+j) with
      | true => rfl
      | false =>
        have hr := hz (n+j) (by omega) hv
        have h := trailing_bit s (n+j) (j-1) (by omega)
        have he : n+j-((j-1)+1)=n := by omega
        rw [he,hs] at h
        cases h
    cases hv : s (n+5) with
    | false => rfl
    | true =>
      apply False.elim
      exact hg.2 (n+1) ⟨hnext 1 (by omega) (by omega),
        by simpa [Nat.add_assoc] using hnext 2 (by omega) (by omega),
        by simpa [Nat.add_assoc] using hnext 3 (by omega) (by omega),
        by simpa [Nat.add_assoc] using hnext 4 (by omega) (by omega),
        by simpa [Nat.add_assoc] using hv⟩
  | true =>
    cases hv : s (n+5) with
    | true => rfl
    | false =>
      have hr := hz (n+5) (by omega) hv
      have hprev (j : Nat) (hj : 1≤j) (hj4 : j≤4) : s (n+j)=true := by
        have h := trailing_bit s (n+5) (4-j) (by omega)
        have he : n+5-((4-j)+1)=n+j := by omega
        simpa only [he] using h
      exact False.elim (hg.2 n ⟨by simpa using hs,hprev 1 (by omega) (by omega),
        hprev 2 (by omega) (by omega),hprev 3 (by omega) (by omega),hprev 4 (by omega) (by omega)⟩)

theorem eventually_periodic_of_critical_bound {s : Nat → Bool} (hg : Golden s)
    (B : Nat) (hb : ∀ n, 5*zeros s n≤n+B) :
    Rule30Jen.EventuallyPeriodic s := by
  have hd : ∀ n, defects s n≤B+4 := by
    intro n
    have hi := count_identity hg n
    have ht := trailing_le_four hg n
    have hc := hb n
    omega
  obtain ⟨N,hN⟩ := monotone_bounded_constant (defects s) (defects_mono s) (B+4) hd
  have hz : ∀ n, N≤n → s n=false → trailing s n=4 := by
    intro n hn hs
    have ha := hN n hn
    have hh := hN (n+1) (by omega)
    simp only [defects,hs,Bool.false_eq_true,↓reduceIte] at hh
    have ht := trailing_le_four hg n
    omega
  exact ⟨N,5,by decide,period_five_of_zero_predecessor hg N hz⟩

theorem aperiodic_excess_unbounded {s : Nat → Bool} (hg : Golden s)
    (ha : ¬ Rule30Jen.EventuallyPeriodic s) (B : Nat) :
    ∃ n, n+B<5*zeros s n := by
  apply Classical.byContradiction
  intro hn
  have hb : ∀ n, 5*zeros s n≤n+B := by
    intro n
    have h : ¬ n+B<5*zeros s n := fun hc => hn ⟨n,hc⟩
    omega
  exact ha (eventually_periodic_of_critical_bound hg B hb)

theorem finite_constrained_excess_unbounded {L : Nat → Bool}
    (hfin : Rule30ZeroBoundary.FinSupp L) (hX : Rule30ZeroBoundary.InX L)
    (hg : Golden (fun k => Rule30ZeroBoundary.zrow L (2*k+1) 1)) (B : Nat) :
    ∃ n, n+B<5*zeros (fun k => Rule30ZeroBoundary.zrow L (2*k+1) 1) n :=
  aperiodic_excess_unbounded hg (Rule30ZeroBoundary.free_not_eventuallyPeriodic hfin hX) B

def CriticalCharge (C B : Nat) (R : Nat → Bool) : Prop := ∀ n,
  5*zeros (Rule30GoldenCoupledResearch.free R) n ≤
    n+B+C*blackCount (Rule30PeriodTwoSideways.Psi R) (2*n+1)

theorem not_finSupp_psi_of_critical_charge {C B : Nat} {R : Nat → Bool}
    (hc : CriticalCharge C B R) :
    ¬ Rule30ZeroBoundary.FinSupp (Rule30PeriodTwoSideways.Psi R) := by
  intro hfin
  obtain ⟨W,hW⟩ := hfin
  have hb : ∀ n, 5*zeros (Rule30GoldenCoupledResearch.free R) n≤n+(B+C*(W+1)) := by
    intro n
    have hcount := blackCount_le_cutoff (W:=W+1) (fun d hd => hW d (by omega)) (2*n+1)
    have hm := Nat.mul_le_mul_left C hcount
    have hcharge := hc n
    omega
  exact Rule30ZeroBoundary.free_not_eventuallyPeriodic ⟨W,hW⟩ (Rule30PeriodTwoSideways.Psi_inX R)
    (eventually_periodic_of_critical_bound (Rule30GoldenCoupledResearch.golden_free R) _ hb)

theorem CQ01_of_critical_charge
    (hc : ∀ R, Rule30ZeroBoundary.FinSupp R → ∃ C B, CriticalCharge C B R) :
    Rule30PeriodTwoCoupled.CQ01 := by
  apply Rule30PeriodTwoSideways.CQ01_iff_Psi.mpr
  intro R hR
  obtain ⟨C,B,hCB⟩ := hc R hR
  exact not_finSupp_psi_of_critical_charge hCB

end Rule30GoldenCriticalDriftResearch
