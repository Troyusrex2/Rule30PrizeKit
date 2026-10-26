import CedarSafetyBridge

/-! Exact unbounded-time boundary semantics for the short-extension argument.
The supplied eight profiles are repeated only for the already-returning prefix;
the extension evolves literally and is not assumed to have period eight. -/
namespace RootShortExtensionCore
open CedarSafetySoundness CedarSafety CedarSafetyBridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def lift8 (p : Profile) (t : Nat) : Bool := profileAt p (t % 8)

def history (p r : Nat → Bool) (v : Bool) : Nat → Bool
  | 0 => v
  | t+1 => xor (history p r v t) (p t || r t)

def driven (p r : Nat → Bool) : Nat → List Bool → List Bool
  | 0, xs => xs
  | t+1, xs => change (p t) (r t) (driven p r t xs)

theorem driven_cons (p r : Nat → Bool) (v : Bool) (vs : List Bool) (t : Nat) :
    driven p r t (v::vs) = history p r v t :: driven (history p r v) p t vs := by
  induction t with
  | zero => rfl
  | succ t ih => rw [driven,ih,change,driven,history]

theorem lift8_zero (t : Nat) : lift8 zero t = false := zero_at _

theorem driven_white (t : Nat) (xs : List Bool) :
    driven (lift8 zero) (lift8 zero) t xs = evolution t xs := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [driven,lift8_zero,ih]
    rfl

theorem profile_zero (p r : Profile) (v : Bool) :
    profileAt (nextProfile p r v) 0 = v := rfl

theorem lift8_next_step (p r : Profile) (v : Bool)
    (hr : (nextProfile p r v).t8 = v) (t : Nat) :
    lift8 (nextProfile p r v) (t+1) =
      xor (lift8 (nextProfile p r v) t) (lift8 p t || lift8 r t) := by
  have ht : t%8<8 := Nat.mod_lt _ (by decide)
  have hs := next_profile_step p r v (t%8) ht
  by_cases he : t%8=7
  · have hnext : (t+1)%8=0 := by omega
    simp only [he] at hs
    unfold lift8
    rw [hnext,he]
    exact (show profileAt (nextProfile p r v) 0=profileAt (nextProfile p r v) 8 from hr.symm).trans hs
  · have hnext : (t+1)%8=t%8+1 := by omega
    simpa only [lift8,hnext] using hs

theorem history_lift8 (p r : Profile) (v : Bool)
    (hr : (nextProfile p r v).t8=v) :
    history (lift8 p) (lift8 r) v = lift8 (nextProfile p r v) := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => rw [history,ih,lift8_next_step p r v hr]

def DrivenSafe (p r : Nat → Bool) (xs : List Bool) : Prop := ∀ t : Nat,
  ¬ ((driven p r t xs).getLastD (p t)=false ∧
     (driven p r (t+1) xs).getLastD (p (t+1))=false)

theorem white_safe (xs : List Bool) (hs : Safe xs) :
    DrivenSafe (lift8 zero) (lift8 zero) xs := by
  intro t
  simpa only [driven_white,lift8_zero,newest] using hs t

theorem safe_cons (p r : Nat → Bool) (v : Bool) (vs : List Bool)
    (hs : DrivenSafe p r (v::vs)) : DrivenSafe (history p r v) p vs := by
  intro t
  simpa only [driven_cons,List.getLastD_cons] using hs t

end RootShortExtensionCore
