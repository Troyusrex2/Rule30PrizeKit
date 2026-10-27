module
public import Ruliology.CellularAutomata.Rule30Prize
public import Rule30ReaderCanonicalResearch

/-! The exact language of the existing canonical-reader DFA, at every width.
This supplies syntax and finite-core facts only; it does not prove the open
canonical trace observer or any prize statement. -/
@[expose] public section
namespace Rule30CanonicalLanguageResearch
open Rule30ReaderCanonicalResearch

def zpad (k : Nat) (xs : List Bool) : List Bool := List.replicate k false ++ xs
def Core (xs : List Bool) : Prop :=
  ∃ k u, u.length ≤ 2 ∧ xs = zpad k u

@[simp] theorem zpad_zero (xs : List Bool) : zpad 0 xs = xs := rfl
@[simp] theorem zpad_succ (k : Nat) (xs : List Bool) :
    zpad (k+1) xs = false :: zpad k xs := by simp [zpad, List.replicate_succ]
@[simp] theorem zpad_length (k : Nat) (xs : List Bool) :
    (zpad k xs).length = k + xs.length := by simp [zpad]

theorem zpad_injective (k : Nat) {xs ys : List Bool}
    (h : zpad k xs = zpad k ys) : xs = ys := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih (List.cons.inj (by simpa only [zpad_succ] using h)).2

theorem zpad_true_injective {k l : Nat} {xs ys : List Bool}
    (h : zpad k (true :: xs) = zpad l (true :: ys)) : k=l ∧ xs=ys := by
  induction k generalizing l with
  | zero =>
    cases l with
    | zero => exact ⟨rfl, (List.cons.inj h).2⟩
    | succ l => simp [zpad_succ] at h
  | succ k ih =>
    cases l with
    | zero => simp [zpad_succ] at h
    | succ l =>
      have hh := ih (List.cons.inj (by simpa only [zpad_succ] using h)).2
      exact ⟨congrArg Nat.succ hh.1, hh.2⟩

theorem phase_injective {k l : Nat} {b c : Bool} {xs ys : List Bool}
    (h : zpad k ([true,b,b] ++ xs) = zpad l ([true,c,c] ++ ys)) :
    k=l ∧ b=c ∧ xs=ys := by
  have hh := zpad_true_injective h
  have h1 := List.cons.inj hh.2
  have h2 := List.cons.inj h1.2
  exact ⟨hh.1, h1.1, h2.2⟩

theorem phase_ne (k l : Nat) (xs ys : List Bool) :
    zpad k ([true,false,false] ++ xs) ≠ zpad l ([true,true,true] ++ ys) := by
  intro h
  have hh := (phase_injective h).2.1
  cases hh

@[simp] theorem phase_length (k : Nat) (b : Bool) (xs : List Bool) :
    (zpad k ([true,b,b] ++ xs)).length = k + 3 + xs.length := by
  simp [Nat.add_comm,Nat.add_left_comm]

theorem core_of_short (xs : List Bool) (h : xs.length ≤ 2) : Core xs :=
  ⟨0, xs, h, rfl⟩

theorem core_false_cons_iff (xs : List Bool) : Core (false::xs) ↔ Core xs := by
  constructor
  · rintro ⟨k,u,hu,he⟩
    cases k with
    | zero =>
      have hh : (false::xs).length = u.length := congrArg List.length he
      exact core_of_short xs (by simp only [List.length_cons] at hh; omega)
    | succ k =>
      exact ⟨k,u,hu,(List.cons.inj (by simpa only [zpad_succ] using he)).2⟩
  · rintro ⟨k,u,hu,he⟩
    exact ⟨k+1,u,hu,by rw [zpad_succ,he]⟩

theorem core_true_cons_iff (xs : List Bool) :
    Core (true::xs) ↔ xs.length ≤ 1 := by
  constructor
  · rintro ⟨k,u,hu,he⟩
    cases k with
    | zero =>
      have hh : (true::xs).length = u.length := congrArg List.length he
      simp only [List.length_cons] at hh
      omega
    | succ k => simp [zpad_succ] at he
  · intro h; exact core_of_short _ (by simp only [List.length_cons]; omega)

@[simp] theorem core_zpad_iff (k : Nat) (xs : List Bool) :
    Core (zpad k xs) ↔ Core xs := by
  induction k with
  | zero => rfl
  | succ k ih => rw [zpad_succ,core_false_cons_iff,ih]

theorem not_core_phase (k : Nat) (b : Bool) (xs : List Bool) :
    ¬ Core (zpad k ([true,b,b] ++ xs)) := by
  rw [core_zpad_iff]
  intro h
  have hh := (core_true_cons_iff (b::b::xs)).mp h
  simp only [List.length_cons] at hh
  omega

theorem crun_five (xs : List Bool) : crun 5 xs = 5 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simpa [crun,cnext,ctable] using ih

theorem crun_six (xs : List Bool) : crun 6 xs = 6 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simpa [crun,cnext,ctable] using ih

theorem canonical_false_cons (xs : List Bool) :
    Canonical (false::xs) ↔ Canonical xs := by rfl

@[simp] theorem canonical_zpad_iff (k : Nat) (xs : List Bool) :
    Canonical (zpad k xs) ↔ Canonical xs := by
  induction k with
  | zero => rfl
  | succ k ih => rw [zpad_succ,canonical_false_cons,ih]

theorem canonical_short (xs : List Bool) (h : xs.length ≤ 2) : Canonical xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs =>
      cases xs with
      | nil => cases a <;> cases b <;> rfl
      | cons c xs => simp only [List.length_cons] at h; omega

theorem canonical_after_first (a b : Bool) (xs : List Bool) :
    Canonical (true::a::b::xs) ↔ a=b ∧ xs≠[] := by
  cases xs with
  | nil => cases a <;> cases b <;> simp [Canonical,crun,cnext,ctable,caccept]
  | cons x xs =>
    cases a <;> cases b <;> cases x <;>
      simp [Canonical,crun,cnext,ctable,caccept,crun_five,crun_six]

@[simp] theorem canonical_phase_iff (k : Nat) (b : Bool) (xs : List Bool) :
    Canonical (zpad k ([true,b,b] ++ xs)) ↔ xs≠[] := by
  rw [canonical_zpad_iff]
  simpa using canonical_after_first b b xs

theorem canonical_iff (xs : List Bool) :
    Canonical xs ↔ Core xs ∨
      (∃ k x, x≠[] ∧ xs=zpad k ([true,false,false] ++ x)) ∨
      (∃ k y, y≠[] ∧ xs=zpad k ([true,true,true] ++ y)) := by
  constructor
  · intro hc
    induction xs with
    | nil => exact Or.inl (core_of_short [] (by decide))
    | cons a xs ih =>
      cases a with
      | false =>
        rcases ih ((canonical_false_cons xs).mp hc) with h | h | h
        · exact Or.inl ((core_false_cons_iff xs).mpr h)
        · obtain ⟨k,x,hx,he⟩ := h
          exact Or.inr (Or.inl ⟨k+1,x,hx,by rw [zpad_succ,he]⟩)
        · obtain ⟨k,x,hx,he⟩ := h
          exact Or.inr (Or.inr ⟨k+1,x,hx,by rw [zpad_succ,he]⟩)
      | true =>
        cases xs with
        | nil => exact Or.inl (core_of_short _ (by decide))
        | cons b xs =>
          cases xs with
          | nil => exact Or.inl (core_of_short _ (by simp))
          | cons c xs =>
            obtain ⟨he,ht⟩ := (canonical_after_first b c xs).mp hc
            subst c
            cases b with
            | false => exact Or.inr (Or.inl ⟨0,xs,ht,rfl⟩)
            | true => exact Or.inr (Or.inr ⟨0,xs,ht,rfl⟩)
  · intro h
    rcases h with h | h | h
    · obtain ⟨k,u,hu,rfl⟩ := h
      exact (canonical_zpad_iff k u).mpr (canonical_short u hu)
    · obtain ⟨k,u,hu,rfl⟩ := h
      exact (canonical_phase_iff k false u).mpr hu
    · obtain ⟨k,u,hu,rfl⟩ := h
      exact (canonical_phase_iff k true u).mpr hu

@[simp] theorem singleStep_zpad (k : Nat) (xs : List Bool) :
    singleStep (zpad k xs) = zpad k (singleStep xs) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [zpad_succ,zpad_succ]
    change false :: singleStep (zpad k xs) = false :: zpad k (singleStep xs)
    rw [ih]

theorem short_step_two (xs : List Bool) (h : xs.length ≤ 2) :
    singleStep (singleStep xs) = xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs =>
      cases xs with
      | nil => cases a <;> cases b <;> rfl
      | cons c xs => simp only [List.length_cons] at h; omega

theorem core_step_two (xs : List Bool) (h : Core xs) : iter xs 2 = xs := by
  obtain ⟨k,u,hu,rfl⟩ := h
  change singleStep (singleStep (zpad k u)) = zpad k u
  rw [singleStep_zpad,singleStep_zpad,short_step_two u hu]

theorem short_observe_injective (xs ys : List Bool)
    (hx : xs.length≤2) (hy : ys.length≤2) (hlen : xs.length=ys.length)
    (h0 : lastBit false xs=lastBit false ys)
    (h1 : lastBit false (singleStep xs)=lastBit false (singleStep ys)) : xs=ys := by
  cases xs with
  | nil => cases ys <;> simp_all
  | cons a xs =>
    cases ys with
    | nil => simp_all
    | cons b ys =>
      cases xs with
      | nil =>
        cases ys with
        | nil => simpa [lastBit] using h0
        | cons c ys => simp_all
      | cons c xs =>
        cases ys with
        | nil => simp_all
        | cons d ys =>
          have hx0 : xs=[] := by cases xs <;> simp_all
          have hy0 : ys=[] := by cases ys <;> simp_all
          subst xs; subst ys
          cases a <;> cases b <;> cases c <;> cases d <;>
            simp_all [singleStep,singleChange,lastBit]

theorem core_observe_injective (xs ys : List Bool)
    (hx : Core xs) (hy : Core ys) (hlen : xs.length=ys.length)
    (h0 : lastBit false xs=lastBit false ys)
    (h1 : lastBit false (singleStep xs)=lastBit false (singleStep ys)) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp_all
    | cons b ys =>
      cases a <;> cases b
      · have he := ih ys ((core_false_cons_iff xs).mp hx)
          ((core_false_cons_iff ys).mp hy) (by simpa using hlen) h0 h1
        exact congrArg (List.cons false) he
      · have hs := (core_true_cons_iff ys).mp hy
        apply short_observe_injective _ _ (by simp only [List.length_cons] at hlen ⊢; omega)
          (by simp only [List.length_cons]; omega) hlen h0 h1
      · have hs := (core_true_cons_iff xs).mp hx
        apply short_observe_injective _ _ (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons] at hlen ⊢; omega) hlen h0 h1
      · have hs := (core_true_cons_iff xs).mp hx
        apply short_observe_injective _ _ (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons] at hlen ⊢; omega) hlen h0 h1

end Rule30CanonicalLanguageResearch
