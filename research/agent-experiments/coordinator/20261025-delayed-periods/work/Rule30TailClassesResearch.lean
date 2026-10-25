import Ruliology.CellularAutomata.Rule30ZeroBoundary
import Ruliology.CellularAutomata.Rule30StripCertificates

namespace Rule30TailClassesResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30StripCertificates

def TailEq (f g : Nat → Bool) : Prop := ∃ D, ∀ d, D≤d → f d=g d

def SpatialPeriod (P : Nat) (f : Nat → Bool) : Prop :=
  ∃ D, ∀ d, D≤d → f (d+P)=f d

theorem seg_eq (n : Nat) (f g : Nat → Bool) (h : seg f n=seg g n) :
    ∀ i, i<n → f i=g i := by
  induction n generalizing f g with
  | zero => intro i hi; omega
  | succ n ih =>
    change f 0 :: seg (fun i => f (i+1)) n = g 0 :: seg (fun i => g (i+1)) n at h
    obtain ⟨h0,ht⟩ := List.cons.inj h
    intro i hi
    cases i with
    | zero => exact h0
    | succ i => exact ih _ _ ht i (by omega)

theorem finite_bound (f : Nat → Nat) (N : Nat) :
    ∃ D, ∀ j, j≤N → f j≤D := by
  induction N with
  | zero =>
    refine ⟨f 0,fun j hj => ?_⟩
    have h : j=0 := by omega
    subst j
    exact Nat.le_refl _
  | succ N ih =>
    obtain ⟨D,hD⟩ := ih
    refine ⟨D+f (N+1),fun j hj => ?_⟩
    by_cases h : j≤N
    · have := hD j h; omega
    · have : j=N+1 := by omega
      subst j; omega

theorem agree_from_window (f g : Nat → Bool) (D P : Nat) (hP : 0<P)
    (hf : ∀ d, D≤d → f (d+P)=f d) (hg : ∀ d, D≤d → g (d+P)=g d)
    (hwin : seg (fun i => f (D+i)) P = seg (fun i => g (D+i)) P) : TailEq f g := by
  have hall : ∀ i, f (D+i)=g (D+i) := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      by_cases hi : i<P
      · exact seg_eq P _ _ hwin i hi
      · rw [show D+i=(D+(i-P))+P by omega,hf _ (by omega),hg _ (by omega)]
        exact ih (i-P) (by omega)
  refine ⟨D,fun d hd => ?_⟩
  simpa [show D+(d-D)=d by omega] using hall (d-D)

/-- Infinitely many distinct tail classes cannot share one eventual period. -/
theorem no_common_period_of_distinct (rows : Nat → Nat → Bool)
    (hd : ∀ m n, m<n → ¬TailEq (rows m) (rows n)) (P : Nat) (hP : 0<P) :
    ¬∀ j, SpatialPeriod P (rows j) := by
  intro hp
  classical
  let threshold (j : Nat) := Classical.choose (hp j)
  have hthreshold (j : Nat) : ∀ d, threshold j≤d → rows j (d+P)=rows j d :=
    Classical.choose_spec (hp j)
  obtain ⟨D,hD⟩ := finite_bound threshold (2^P)
  let window (j : Nat) := seg (fun i => rows j (D+i)) P
  obtain ⟨m,n,hmn,hn,hwin⟩ := Rule30Jen.pigeonhole P window
    (fun j => length_seg P _)
  apply hd m n hmn
  exact agree_from_window _ _ D P hP
    (fun d h => hthreshold m d (by have := hD m (by omega); omega))
    (fun d h => hthreshold n d (by have := hD n hn; omega)) hwin

theorem tail_recon_time {a b : Nat → Bool}
    (h : TailEq (fun d => recon a d 0) (fun d => recon b d 0)) (t : Nat) :
    TailEq (fun d => recon a d t) (fun d => recon b d t) := by
  obtain ⟨D,hD⟩ := h
  refine ⟨D+1+t,fun d hd => ?_⟩
  have hlocal := zrow_local (L:=lam a) (L':=lam b) (a:=D+1)
    (by omega) (fun k hk => hD k (by omega)) t d hd
  simpa only [zrow_lam] using hlocal

end Rule30TailClassesResearch
