import CedarSafetySoundness

namespace CedarSafety
open CedarSafetySoundness

def newest (xs : List Bool) : Bool := xs.getLastD false

/-- Exact all-time safety predicate requested in the follow-up, including []. -/
def Safe (xs : List Bool) : Prop := ∀ t : Nat,
  ¬ (newest (evolution t xs) = false ∧ newest (evolution (t+1) xs) = false)

def EightWindow (xs : List Bool) : Prop := ∀ t : Fin 8,
  ¬ (newest (evolution t.val xs) = false ∧ newest (evolution (t.val+1) xs) = false)

def profileAt (p : Profile) : Nat → Bool
  | 0 => p.t0
  | 1 => p.t1
  | 2 => p.t2
  | 3 => p.t3
  | 4 => p.t4
  | 5 => p.t5
  | 6 => p.t6
  | 7 => p.t7
  | 8 => p.t8
  | _ => false

def ProfileSafe (p : Profile) : Prop := ∀ t : Fin 8,
  ¬ (profileAt p t.val = false ∧ profileAt p (t.val+1) = false)

instance (p : Profile) : Decidable (ProfileSafe p) :=
  inferInstanceAs (Decidable (∀ t : Fin 8,
    ¬ (profileAt p t.val = false ∧ profileAt p (t.val+1) = false)))

def profileTrace (p r : Profile) : List Bool → Profile
  | [] => p
  | v :: vs => profileTrace (nextProfile p r v) p vs

/-- Actual time-t row with supplied older profiles; only t<=8 is used. -/
def slice (p r : Profile) : Nat → List Bool → List Bool
  | 0, xs => xs
  | t+1, xs => change (profileAt p t) (profileAt r t) (slice p r t xs)

theorem next_profile_step (p r : Profile) (v : Bool) (t : Nat) (ht : t < 8) :
    profileAt (nextProfile p r v) (t+1) =
      xor (profileAt (nextProfile p r v) t) (profileAt p t || profileAt r t) := by
  have h : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> subst t <;> rfl

theorem slice_nil (p r : Profile) (t : Nat) : slice p r t [] = [] := by
  induction t with
  | zero => rfl
  | succ t ih => simp [slice,ih,change]

theorem slice_cons (p r : Profile) (v : Bool) (vs : List Bool) (t : Nat) (ht : t ≤ 8) :
    slice p r t (v::vs) = profileAt (nextProfile p r v) t :: slice (nextProfile p r v) p t vs := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [slice,ih (by omega),change,next_profile_step p r v t (by omega),slice]

theorem profile_trace_last (xs : List Bool) (p r : Profile) (t : Nat) (ht : t ≤ 8) :
    (slice p r t xs).getLastD (profileAt p t) = profileAt (profileTrace p r xs) t := by
  induction xs generalizing p r with
  | nil => simp [profileTrace,slice_nil]
  | cons v vs ih =>
    rw [slice_cons p r v vs t ht,List.getLastD_cons]
    exact ih (nextProfile p r v) p

theorem zero_at (t : Nat) : profileAt zero t = false := by
  unfold profileAt
  split <;> rfl

theorem slice_white (t : Nat) (xs : List Bool) : slice zero zero t xs = evolution t xs := by
  induction t with
  | zero => rfl
  | succ t ih => simp [slice,zero_at,ih,evolution,F]

theorem trace_white (xs : List Bool) (t : Nat) (ht : t ≤ 8) :
    profileAt (profileTrace zero zero xs) t = newest (evolution t xs) := by
  rw [← profile_trace_last xs zero zero t ht,slice_white,zero_at]
  rfl

theorem profile_safe_iff_window (xs : List Bool) :
    ProfileSafe (profileTrace zero zero xs) ↔ EightWindow xs := by
  unfold ProfileSafe EightWindow
  constructor <;> intro h t
  · simpa only [trace_white xs t.val (by omega),trace_white xs (t.val+1) (by omega)] using h t
  · simpa only [trace_white xs t.val (by omega),trace_white xs (t.val+1) (by omega)] using h t

theorem evolution_add (s t : Nat) (xs : List Bool) :
    evolution (s+t) xs = evolution s (evolution t xs) := by
  induction s with
  | zero => simp [evolution]
  | succ s ih => simpa [Nat.succ_add,evolution] using congrArg F ih

theorem return8_periodic {xs : List Bool} (hr : evolution 8 xs = xs) (t : Nat) :
    evolution (t+8) xs = evolution t xs := by
  rw [evolution_add,hr]

theorem safe_iff_window_of_return8 {xs : List Bool} (hr : evolution 8 xs = xs) :
    Safe xs ↔ EightWindow xs := by
  constructor
  · intro h t
    exact h t.val
  · intro h
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
      by_cases small : t < 8
      · exact h ⟨t,small⟩
      · have ht : 8 ≤ t := by omega
        have previous := ih (t-8) (by omega)
        rw [show t=(t-8)+8 by omega,return8_periodic hr,
          show (t-8)+8+1=((t-8)+1)+8 by omega,return8_periodic hr]
        exact previous

theorem not_safe_nil : ¬ Safe [] := by
  intro h
  exact h 0 ⟨rfl,rfl⟩

end CedarSafety
