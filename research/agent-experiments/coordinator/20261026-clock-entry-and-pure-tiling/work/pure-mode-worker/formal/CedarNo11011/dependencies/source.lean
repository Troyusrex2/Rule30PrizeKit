import CedarSafetySemantics

/-! A forbidden temporal cylinder under four shared OR recurrences.
No period, safety or ancestry-completeness assumption is made. -/
namespace CedarNo11011
open CedarSafetySoundness CedarSafety
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev Trace := Nat → Bool
def Step4 (b a u : Trace) : Prop :=
  ∀ t : Nat, t < 4 → xor (b t) (b (t+1)) = (a t || u t)
def Pattern (b : Trace) : Prop :=
  b 0 = true ∧ b 1 = true ∧ b 2 = false ∧ b 3 = true ∧ b 4 = true

instance (b : Trace) : Decidable (Pattern b) := by
  unfold Pattern
  infer_instance

theorem or_false_parts (a b : Bool) (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

theorem absorb_true : ∀ a b c : Bool, (a || b) = true →
    a = (b || c) → a = true := by
  decide +kernel

theorem local_no11011 (B A u v w z : Trace)
    (hB : Step4 B A u) (hA : Step4 A u v)
    (hu : Step4 u v w) (hv : Step4 v w z) : ¬ Pattern B := by
  rintro ⟨b0,b1,b2,b3,b4⟩
  have e0 : (A 0 || u 0) = false := by
    simpa [b0,b1] using (hB 0 (by decide)).symm
  have e3 : (A 3 || u 3) = false := by
    simpa [b3,b4] using (hB 3 (by decide)).symm
  obtain ⟨a0,u0⟩ := or_false_parts _ _ e0
  obtain ⟨a3,u3⟩ := or_false_parts _ _ e3
  have e2 : (A 2 || u 2) = true := by
    simpa [b2,b3] using (hB 2 (by decide)).symm
  have ea2 : A 2 = (u 2 || v 2) := by
    simpa [a3] using hA 2 (by decide)
  have a2 : A 2 = true := absorb_true _ _ _ e2 ea2
  have eu2 : u 2 = (v 2 || w 2) := by
    simpa [u3] using hu 2 (by decide)
  have u2 : u 2 = true := absorb_true _ _ _ (ea2.symm.trans a2) eu2
  cases a1 : A 1 with
  | false =>
    have u1 : u 1 = true := by
      simpa [b1,b2,a1] using (hB 1 (by decide)).symm
    have v0 : v 0 = false := by
      simpa [a0,a1,u0] using (hA 0 (by decide)).symm
    have ev1 : (v 1 || w 1) = false := by
      simpa [u1,u2] using (hu 1 (by decide)).symm
    have v1 : v 1 = false := (or_false_parts _ _ ev1).1
    have w0 : w 0 = true := by
      simpa [u0,u1,v0] using (hu 0 (by decide)).symm
    have bad := hv 0 (by decide)
    simpa [v0,v1,w0] using bad
  | true =>
    have v0 : v 0 = true := by
      simpa [a0,a1,u0] using (hA 0 (by decide)).symm
    have eu1 : (u 1 || v 1) = false := by
      simpa [a1,a2] using (hA 1 (by decide)).symm
    have u1 : u 1 = false := (or_false_parts _ _ eu1).1
    have bad := hu 0 (by decide)
    simpa [u0,u1,v0] using bad

theorem next_profile_step4 (p r : Profile) (v : Bool) :
    Step4 (profileAt (nextProfile p r v)) (profileAt p) (profileAt r) := by
  intro t ht
  rw [next_profile_step p r v t (by omega)]
  cases profileAt (nextProfile p r v) t <;>
    cases (profileAt p t || profileAt r t) <;> rfl

theorem four_profile_no11011 (p r : Profile) (a b c d : Bool) :
    ¬ Pattern (profileAt (profileTrace p r [a,b,c,d])) := by
  let v := nextProfile p r a
  let u := nextProfile v p b
  let A := nextProfile u v c
  let B := nextProfile A u d
  exact local_no11011 (profileAt B) (profileAt A) (profileAt u)
    (profileAt v) (profileAt p) (profileAt r)
    (next_profile_step4 A u d) (next_profile_step4 u v c)
    (next_profile_step4 v p b) (next_profile_step4 p r a)

theorem long_profile_no11011 (xs : List Bool) :
    ∀ p r : Profile, 4 ≤ xs.length → ¬ Pattern (profileAt (profileTrace p r xs)) := by
  induction xs with
  | nil => intro p r h; simp at h
  | cons a xs ih =>
    intro p r h
    by_cases ht : 4 ≤ xs.length
    · exact ih (nextProfile p r a) p ht
    · cases xs with
      | nil => simp at h
      | cons b xs =>
        cases xs with
        | nil => simp at h
        | cons c xs =>
          cases xs with
          | nil => simp at h
          | cons d xs =>
            cases xs with
            | nil => exact four_profile_no11011 p r a b c d
            | cons e xs => simp at ht

theorem white_profile_no11011 (xs : List Bool) :
    ¬ Pattern (profileAt (profileTrace zero zero xs)) := by
  by_cases h : 4 ≤ xs.length
  · exact long_profile_no11011 xs zero zero h
  · cases xs with
    | nil => decide +kernel
    | cons a xs =>
      cases xs with
      | nil => cases a <;> decide +kernel
      | cons b xs =>
        cases xs with
        | nil => cases a <;> cases b <;> decide +kernel
        | cons c xs =>
          cases xs with
          | nil => cases a <;> cases b <;> cases c <;> decide +kernel
          | cons d xs => simp at h

theorem finite_white_no11011_at_zero (xs : List Bool) :
    ¬ (newest (evolution 0 xs) = true ∧ newest (evolution 1 xs) = true ∧
      newest (evolution 2 xs) = false ∧ newest (evolution 3 xs) = true ∧
      newest (evolution 4 xs) = true) := by
  have h := white_profile_no11011 xs
  unfold Pattern at h
  simpa only [trace_white xs 0 (by decide),trace_white xs 1 (by decide),
    trace_white xs 2 (by decide),trace_white xs 3 (by decide),
    trace_white xs 4 (by decide)] using h

theorem finite_white_no11011 (xs : List Bool) (t : Nat) :
    ¬ (newest (evolution t xs) = true ∧ newest (evolution (t+1) xs) = true ∧
      newest (evolution (t+2) xs) = false ∧ newest (evolution (t+3) xs) = true ∧
      newest (evolution (t+4) xs) = true) := by
  have h := finite_white_no11011_at_zero (evolution t xs)
  simpa only [← evolution_add,Nat.zero_add,Nat.add_zero,Nat.add_comm] using h

end CedarNo11011
