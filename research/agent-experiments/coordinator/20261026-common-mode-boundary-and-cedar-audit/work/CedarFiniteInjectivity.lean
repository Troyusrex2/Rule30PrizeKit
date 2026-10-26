import CedarSafetyBridge

namespace CedarFiniteInjectivity
open CedarSafetySoundness CedarSafety CedarSafetyBridge

theorem xor_right_cancel (x y mask : Bool) (h : xor x mask = xor y mask) : x = y := by
  cases x <;> cases y <;> cases mask <;> simp_all

/-- Each simultaneous triangular output recovers its input older-first. -/
theorem change_injective (p r : Bool) {xs ys : List Bool}
    (h : change p r xs = change p r ys) : xs = ys := by
  induction xs generalizing p r ys with
  | nil => cases ys <;> simp_all [change]
  | cons x xs ih =>
    cases ys with
    | nil => simp [change] at h
    | cons y ys =>
      simp only [change,List.cons.injEq] at h
      have he := xor_right_cancel x y (p || r) h.1
      subst y
      exact congrArg (List.cons x) (ih x p h.2)

theorem F_injective {xs ys : List Bool} (h : F xs = F ys) : xs = ys :=
  change_injective false false h

theorem evolution_injective (t : Nat) {xs ys : List Bool}
    (h : evolution t xs = evolution t ys) : xs = ys := by
  induction t with
  | zero => exact h
  | succ t ih => exact ih (F_injective h)

/-- Eventual entry into an eight-returning state forces the original word
to return after eight. No state-space census or clock bound is used. -/
theorem return8_of_eventual_return8 (xs : List Bool) (t : Nat)
    (h : evolution 8 (evolution t xs) = evolution t xs) : evolution 8 xs = xs := by
  apply evolution_injective t
  calc
    evolution t (evolution 8 xs) = evolution 8 (evolution t xs) := by
      rw [← evolution_add,← evolution_add,Nat.add_comm t 8]
    _ = evolution t xs := h

theorem return8_of_eventual_accepted (xs : List Bool) (t : Nat)
    (h : accepted (CedarSafetySoundness.read 0 (evolution t xs)) = true) :
    evolution 8 xs = xs :=
  return8_of_eventual_return8 xs t (accepted_return_eight (evolution t xs) h)

theorem accepted_of_safe_eventual_accepted (xs : List Bool) (t : Nat) (hs : Safe xs)
    (h : accepted (CedarSafetySoundness.read 0 (evolution t xs)) = true) :
    accepted (CedarSafetySoundness.read 0 xs) = true :=
  (safe_return_iff_accepted xs).mp ⟨hs,return8_of_eventual_accepted xs t h⟩

end CedarFiniteInjectivity
