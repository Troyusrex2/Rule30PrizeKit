import Rule30TailClassesResearch

namespace Rule30PeriodicReconstructionResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30StripCertificates Rule30TailClassesResearch

theorem periodic_window_ext (T P : Nat) (hP : 0<P) (f g : Nat → Bool)
    (hf : ∀ t, T≤t → f (t+P)=f t) (hg : ∀ t, T≤t → g (t+P)=g t)
    (hwin : ∀ t, t<T+P → f t=g t) : ∀ t, f t=g t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases ht : t<T+P
    · exact hwin t ht
    · rw [show t=(t-P)+P by omega,hf _ (by omega),hg _ (by omega)]
      exact ih (t-P) (by omega)

theorem recon_time_period (a : Nat → Bool) (T P : Nat)
    (hper : ∀ t, T≤t → a (t+P)=a t) (d t : Nat) (ht : T≤t) :
    recon a d (t+P)=recon a d t := by
  rw [recon_shift]
  apply recon_local
  intro j hj
  simpa [Nat.add_assoc] using hper (t+j) (by omega)

def profile (a : Nat → Bool) (W d : Nat) :=
  seg (fun i => if i<W then recon a d i else recon a (d+1) (i-W)) (2*W)

theorem profile_eq (a : Nat → Bool) (T P : Nat) (hP : 0<P)
    (hper : ∀ t, T≤t → a (t+P)=a t) (m n : Nat)
    (h : profile a (T+P) m=profile a (T+P) n) :
    (∀ t, recon a m t=recon a n t) ∧
    (∀ t, recon a (m+1) t=recon a (n+1) t) := by
  have hfirst : ∀ t, t<T+P → recon a m t=recon a n t := by
    intro t ht
    have he := seg_eq (2*(T+P)) _ _ h t (by omega)
    simpa only [ite_eq_left ht] using he
  have hsecond : ∀ t, t<T+P → recon a (m+1) t=recon a (n+1) t := by
    intro t ht
    have he := seg_eq (2*(T+P)) _ _ h (T+P+t) (by omega)
    simpa only [ite_eq_right (show ¬T+P+t<T+P by omega),Nat.add_sub_cancel_left] using he
  exact ⟨periodic_window_ext T P hP _ _ (recon_time_period a T P hper m)
      (recon_time_period a T P hper n) hfirst,
    periodic_window_ext T P hP _ _ (recon_time_period a T P hper (m+1))
      (recon_time_period a T P hper (n+1)) hsecond⟩

/-- An eventually periodic temporal input reconstructs an eventually
periodic spatial start. The bound may depend on the temporal transient. -/
theorem spatial_of_temporal (a : Nat → Bool) (T P : Nat) (hP : 0<P)
    (hper : ∀ t, T≤t → a (t+P)=a t) :
    Rule30Jen.EventuallyPeriodic (fun d => recon a d 0) := by
  obtain ⟨m,n,hmn,hn,he⟩ := Rule30Jen.pigeonhole (2*(T+P)) (profile a (T+P))
    (fun d => length_seg _ _)
  have hpair := profile_eq a T P hP hper m n he
  have key : ∀ q, (∀ t, recon a (m+q) t=recon a (n+q) t) ∧
      (∀ t, recon a (m+q+1) t=recon a (n+q+1) t) := by
    intro q
    induction q with
    | zero => simpa using hpair
    | succ q ih =>
      refine ⟨?_,fun t => ?_⟩
      · simpa [Nat.add_assoc] using ih.2
      · rw [show m+(q+1)+1=m+q+2 by omega,
          show n+(q+1)+1=n+q+2 by omega,recon_two,recon_two,ih.2,ih.2,ih.1]
  refine ⟨m,n-m,by omega,fun d hd => ?_⟩
  have h := (key (d-m)).1 0
  rw [show m+(d-m)=d by omega,show n+(d-m)=d+(n-m) by omega] at h
  exact h.symm

end Rule30PeriodicReconstructionResearch
