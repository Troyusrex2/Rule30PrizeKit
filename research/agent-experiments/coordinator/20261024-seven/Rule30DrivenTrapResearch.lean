import Rule30ExternalAbsorbedPrefixesAudit

/-! Reusable entry criteria for the coupled period-two route. The trap entry
or eventual prefix match remains an explicit hypothesis. No assertion that
every finite right half, or the empty right half, reaches such a state. -/

namespace Rule30DrivenTrapResearch
open Ruliology.CellularAutomata
open Rule30Jen (EventuallyPeriodic)
open Rule30ZeroBoundary (FinSupp)
open Rule30Ether (ether ether_period drv drv_isR30 rowOf wallStates trap_invariant)
open Rule30PeriodTwoCoupled (altCol)
open Rule30PeriodTwoSideways (u Psi drv_shift not_finSupp_Psi_of_eventuallyPeriodic)

theorem visible_periodic_of_trap (R : Nat → Bool) (j0 s k t1 : Nat)
    (hk : (j0+k)%7 = 2) (hk1 : 1 ≤ k)
    (h0 : ∀ t, t1 ≤ t → drv altCol R t 0 = ether j0 (t+s))
    (hE : ∀ p, 1 ≤ p → p ≤ k → drv altCol R t1 p = ether (j0+p) (t1+s))
    (hW : ((t1+s)%4, rowOf (drv altCol R) t1 k 13) ∈ wallStates) :
    EventuallyPeriodic (u R) := by
  have inv := trap_invariant (drv_isR30 altCol R) j0 s k t1 hk h0 hE hW
  have col : ∀ t, t1 ≤ t → drv altCol R t 1 = ether (j0+1) (t+s) := by
    intro t ht
    have h := (inv (t-t1)).1 1 hk1
    simpa only [show t1+(t-t1) = t by omega] using h
  refine ⟨t1,2,by decide,?_⟩
  intro t ht
  change drv altCol R (2*(t+2)+1) 1 = drv altCol R (2*t+1) 1
  rw [col _ (by omega), col _ (by omega),
      show 2*(t+2)+1+s = (2*t+1+s)+4 by omega, ether_period]

theorem not_finSupp_Psi_of_trap (R : Nat → Bool) (j0 s k t1 : Nat)
    (hk : (j0+k)%7 = 2) (hk1 : 1 ≤ k)
    (h0 : ∀ t, t1 ≤ t → drv altCol R t 0 = ether j0 (t+s))
    (hE : ∀ p, 1 ≤ p → p ≤ k → drv altCol R t1 p = ether (j0+p) (t1+s))
    (hW : ((t1+s)%4, rowOf (drv altCol R) t1 k 13) ∈ wallStates) :
    ¬ FinSupp (Psi R) :=
  not_finSupp_Psi_of_eventuallyPeriodic R (visible_periodic_of_trap R j0 s k t1 hk hk1 h0 hE hW)

def rightAt (R : Nat → Bool) (q : Nat) : Nat → Bool := fun p => drv altCol R (2*q) p

theorem u_rightAt (R : Nat → Bool) (q v : Nat) : u (rightAt R q) v = u R (q+v) := by
  unfold u rightAt
  rw [show 2*(q+v)+1 = 2*q+(2*v+1) by omega, drv_shift altCol R (2*q) (2*v+1) 1]
  have hc : (fun t => altCol (2*q+t)) = altCol := by
    funext t
    unfold altCol
    rw [show (2*q+t)%2 = t%2 by omega]
  rw [hc]

theorem visible_periodic_of_rightAt (R : Nat → Bool) (q : Nat)
    (hp : EventuallyPeriodic (u (rightAt R q))) : EventuallyPeriodic (u R) := by
  obtain ⟨T,P,hP,hper⟩ := hp
  refine ⟨q+T,P,hP,?_⟩
  intro t ht
  have h := hper (t-q) (by omega)
  rw [u_rightAt, u_rightAt] at h
  simpa only [show q+(t-q+P) = t+P by omega, show q+(t-q) = t by omega] using h

theorem not_finSupp_Psi_of_even_prefix31 (R : Nat → Bool) (q : Nat)
    (h : Rule30Submission.AgreesPrefix 28 (rightAt R q) Rule30Submission.R31) :
    ¬ FinSupp (Psi R) := by
  apply not_finSupp_Psi_of_eventuallyPeriodic R
  apply visible_periodic_of_rightAt R q
  exact ⟨0,2,by decide,fun t _ => by
    rw [Rule30Submission.u_prefix31 _ h, Rule30Submission.u_prefix31 _ h]
    simp⟩

theorem not_finSupp_Psi_of_even_prefix495 (R : Nat → Bool) (q : Nat)
    (h : Rule30Submission.AgreesPrefix 24 (rightAt R q) Rule30Submission.R495) :
    ¬ FinSupp (Psi R) := by
  apply not_finSupp_Psi_of_eventuallyPeriodic R
  apply visible_periodic_of_rightAt R q
  exact ⟨0,2,by decide,fun t _ => by
    rw [Rule30Submission.u_prefix495 _ h, Rule30Submission.u_prefix495 _ h]
    simp⟩

end Rule30DrivenTrapResearch
