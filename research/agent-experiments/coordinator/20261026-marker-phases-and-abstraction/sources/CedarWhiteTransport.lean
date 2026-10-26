import CedarSafetySemantics

namespace CedarWhiteTransport
open CedarSafetySoundness CedarSafety

/-- Genuine older prefixes evolve autonomously under the same white boundary. -/
theorem take_change (p r : Bool) (n : Nat) (xs : List Bool) :
    (change p r xs).take n = change p r (xs.take n) := by
  induction n generalizing p r xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons v vs =>
      change xor v (p || r) :: (change v p vs).take n =
        xor v (p || r) :: change v p (vs.take n)
      rw [ih]

theorem take_F (xs : List Bool) (n : Nat) : (F xs).take n = F (xs.take n) :=
  take_change false false n xs

theorem take_evolution (xs : List Bool) (n t : Nat) :
    (evolution t xs).take n = evolution t (xs.take n) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [evolution,take_F,ih,evolution]

theorem evolution_false_cons (xs : List Bool) (t : Nat) :
    evolution t (false :: xs) = false :: evolution t xs := by
  induction t with
  | zero => rfl
  | succ t ih => rw [evolution,ih]; rfl

theorem safe_false_cons (xs : List Bool) : Safe (false :: xs) ↔ Safe xs := by
  unfold Safe newest
  simp only [evolution_false_cons,List.getLastD_cons]

theorem return8_false_cons (xs : List Bool) :
    evolution 8 (false :: xs) = false :: xs ↔ evolution 8 xs = xs := by
  rw [evolution_false_cons,List.cons.injEq]
  simp

/-- Removing any inert leading white padding preserves the exact safety predicate. -/
theorem safe_white_padding (xs : List Bool) (k : Nat) :
    Safe (List.replicate k false ++ xs) ↔ Safe xs := by
  induction k with
  | zero => simp
  | succ k ih => simpa only [List.replicate_succ,List.cons_append,safe_false_cons] using ih

theorem return8_white_padding (xs : List Bool) (k : Nat) :
    evolution 8 (List.replicate k false ++ xs) = List.replicate k false ++ xs ↔
      evolution 8 xs = xs := by
  induction k with
  | zero => simp
  | succ k ih => simpa only [List.replicate_succ,List.cons_append,return8_false_cons] using ih

/-- After dropping two output cells, a single update forgets supplied older boundary bits. -/
theorem change_drop_two (p r p' r' : Bool) (xs : List Bool) :
    (change p r xs).drop 2 = (change p' r' xs).drop 2 := by
  cases xs with
  | nil => rfl
  | cons a vs => cases vs <;> rfl

theorem change_drop (p r : Bool) (n : Nat) (xs : List Bool) :
    (change p r xs).drop (n+2) = (F (xs.drop n)).drop 2 := by
  induction n generalizing p r xs with
  | zero => exact change_drop_two p r false false xs
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons v vs =>
      change (change v p vs).drop (n+2) = (F (vs.drop n)).drop 2
      exact ih v p vs

theorem F_drop (xs : List Bool) (n : Nat) :
    (F xs).drop (n+2) = (F (xs.drop n)).drop 2 := change_drop false false n xs

/-- Exact finite-cone transport, derived from the literal parallel F.
After t updates, discarding n initial older cells can affect only the first
2t cells of the retained suffix. No boundary clock is assumed. -/
theorem evolution_drop_cone (xs : List Bool) (n t : Nat) :
    (evolution t xs).drop (n+2*t) = (evolution t (xs.drop n)).drop (2*t) := by
  induction t with
  | zero => simp [evolution]
  | succ t ih =>
    rw [evolution,evolution,
      show n+2*(t+1)=(n+2*t)+2 by omega,
      show 2*(t+1)=2*t+2 by omega,
      F_drop (evolution t xs) (n+2*t),
      F_drop (evolution t (xs.drop n)) (2*t),ih]

/-- Arbitrary older inputs transport through a common finite suffix exactly
outside its radius-two-per-step dependency cone. -/
theorem common_suffix_transport (xs ys : List Bool) (n m t : Nat)
    (h : xs.drop n = ys.drop m) :
    (evolution t xs).drop (n+2*t) = (evolution t ys).drop (m+2*t) := by
  rw [evolution_drop_cone,evolution_drop_cone,h]

theorem prefix_transport (older xs : List Bool) (t : Nat) :
    (evolution t (older ++ xs)).drop (older.length+2*t) =
      (evolution t xs).drop (2*t) := by
  rw [evolution_drop_cone,List.drop_left]

end CedarWhiteTransport
