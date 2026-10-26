module
public import Rule30SaturatedOrPeriodResearch

/-! A periodic OR trace supplies the periods of two newer profiles.
This strengthens the saturated-OR premise; no physical-center claim. -/
@[expose] public section
namespace Rule30PeriodicOrPeriodResearch
open Rule30CommonPastResearch
open Rule30OrClockObserverResearch (shift_flag)
open Rule30EvenModeRigidityResearch
open Rule30SaturatedOrPeriodResearch (anti_double anti_has_black)
set_option maxHeartbeats 4000000

theorem actual_periodic_or_double_period
    (a : Nat → Nat → Bool) (ha : Actual a) (j R : Nat)
    (hk : ∀ t, a (t+R) (j+3)=xor (a t (j+3)) true)
    (hl : ∀ t, a (t+R) (j+2)=a t (j+2))
    (ho : ∀ t, (a (t+R) (j+5) || a (t+R) (j+4))=
      (a t (j+5) || a t (j+4))) :
    (∀ t, a (t+2*R) (j+4)=a t (j+4)) ∧
    (∀ t, a (t+2*R) (j+5)=a t (j+5)) := by
  let g := fun t => a t (j+5)
  let h := fun t => a t (j+4)
  let k := fun t => a t (j+3)
  let l := fun t => a t (j+2)
  have oh : ∀ t, (g (t+2*R) || h (t+2*R))=(g t || h t) := by
    intro t
    change (a (t+2*R) (j+5) || a (t+2*R) (j+4))=(a t (j+5) || a t (j+4))
    rw [show t+2*R=(t+R)+R by omega,ho (t+R),ho t]
  have gs : ∀ t, g (t+1)=xor (g t) (h t || k t) := fun t => ha t (j+5)
  have hs : ∀ t, h (t+1)=xor (h t) (k t || l t) := fun t => ha t (j+4)
  have kp : ∀ t, k (t+2*R)=k t := anti_double k R hk
  have lp : ∀ t, l (t+2*R)=l t := by
    intro t
    change a (t+2*R) (j+2)=a t (j+2)
    rw [show t+2*R=(t+R)+R by omega,hl (t+R),hl t]
  have hf := shift_flag h (fun t => k t || l t) (2*R) hs (by
    intro t; rw [kp t,lp t])
  have hp : ∀ t, h (t+2*R)=h t := by
    cases he : xor (h (2*R)) (h 0) with
    | false =>
      intro t
      simpa only [he,Bool.xor_false] using hf t
    | true =>
      have hh : ∀ t, a (t+2*R) ((j+1)+3)=xor (a t ((j+1)+3)) true := by
        intro t
        simpa only [he,show j+1+3=j+4 by omega] using hf t
      have kk : ∀ t, a (t+2*R) ((j+1)+2)=a t ((j+1)+2) := by
        intro t
        simpa only [show j+1+2=j+3 by omega] using kp t
      have bad := actual_even_plateau_or_clock_rigidity a ha (j+1) R hh kk
      exfalso
      apply bad
      intro t
      simpa only [show j+1+4=j+5 by omega,show j+1+3=j+4 by omega] using oh t
  have hz : ∃ s, h s=false := by
    obtain ⟨s,hsk⟩ := anti_has_black k R hk
    cases he : h s with
    | false => exact ⟨s,he⟩
    | true =>
      refine ⟨s+1,?_⟩
      rw [hs s,he,hsk]
      rfl
  have gf := shift_flag g (fun t => h t || k t) (2*R) gs (by
    intro t; rw [hp t,kp t])
  obtain ⟨s,hzs⟩ := hz
  have hb : h (s+2*R)=false := (hp s).trans hzs
  have geq : g (s+2*R)=g s := by
    have he := oh s
    simpa only [hb,hzs,Bool.or_false] using he
  have ge := gf s
  rw [geq] at ge
  have flag : xor (g (2*R)) (g 0)=false := by
    have gate : ∀ b e : Bool, b=xor b e → e=false := by decide
    exact gate _ _ ge
  refine ⟨hp,?_⟩
  intro t
  simpa only [flag,Bool.xor_false] using gf t

end Rule30PeriodicOrPeriodResearch
