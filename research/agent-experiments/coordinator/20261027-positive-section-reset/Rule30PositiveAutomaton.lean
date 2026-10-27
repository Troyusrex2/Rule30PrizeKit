import Ruliology.CellularAutomata.Rule30Prize
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
Positive monoid freeness for the three finite-word states of Rule 30.
Inputs are older-first. Products act right to left and sections are input-indexed.
This is the elementary reset/cancellation argument of Silva and Steinberg,
"On a Class of Automata Groups Generalizing Lamplighter Groups", specialized
to the two-bit reset table below. No reader-completeness statement is made.
-/

namespace Rule30PositiveAutomaton

inductive State where
  | A | B | C
  deriving DecidableEq

open State

def flip : State → Bool
  | A => false
  | B | C => true

def next : State → Bool → State
  | A, false => A
  | B, false => A
  | C, false => B
  | _, true => C

def act (q : State) : List Bool → List Bool
  | [] => []
  | b :: bs => Bool.xor b (flip q) :: act (next q b) bs

def memory (previous older : Bool) : State :=
  if previous then C else if older then B else A

def ruleScan (previous older : Bool) : List Bool → List Bool
  | [] => []
  | b :: bs => Ruliology.CellularAutomata.Rule30Jen.rule b previous older ::
      ruleScan b previous bs

/-- The automaton is literally the Rule30 xor/or scan with raw older memory. -/
theorem act_memory (previous older : Bool) (xs : List Bool) :
    act (memory previous older) xs = ruleScan previous older xs := by
  induction xs generalizing previous older with
  | nil => rfl
  | cons b bs ih =>
    have hf : flip (memory previous older) = (previous || older) := by
      cases previous <;> cases older <;> rfl
    have hn : next (memory previous older) b = memory b previous := by
      cases previous <;> cases older <;> cases b <;> rfl
    simp only [act, ruleScan, hn, ih, hf, Ruliology.CellularAutomata.Rule30Jen.rule]

theorem act_A_eq_ruleScan (xs : List Bool) :
    act A xs = ruleScan false false xs := by
  exact act_memory false false xs

def undo (q : State) : List Bool → List Bool
  | [] => []
  | b :: bs =>
    let x := Bool.xor b (flip q)
    x :: undo (next q x) bs

theorem act_undo (q : State) (xs : List Bool) : act q (undo q xs) = xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
    cases q <;> cases b <;> simp [act, undo, flip, next, ih]

theorem undo_act (q : State) (xs : List Bool) : undo q (act q xs) = xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
    cases q <;> cases b <;> simp [act, undo, flip, next, ih]

theorem act_bijective (q : State) : Function.Bijective (act q) := by
  constructor
  · intro x y h
    have h' := congrArg (undo q) h
    simpa only [undo_act] using h'
  · intro x
    exact ⟨undo q x, act_undo q x⟩

def run : List State → List Bool → List Bool
  | [], xs => xs
  | q :: qs, xs => act q (run qs xs)

def Equivalent (u v : List State) : Prop := ∀ xs, run u xs = run v xs

theorem run_append (u v : List State) (xs : List Bool) :
    run (u ++ v) xs = run u (run v xs) := by
  induction u with
  | nil => rfl
  | cons q qs ih => simp only [List.cons_append, run, ih]

theorem cancel_right (u v : List State) (q : State)
    (h : Equivalent (u ++ [q]) (v ++ [q])) : Equivalent u v := by
  intro xs
  have hx := h (undo q xs)
  simpa only [run_append, run, act_undo] using hx

def sectionState (q : State) : List Bool → State
  | [] => q
  | b :: bs => sectionState (next q b) bs

def sections : List State → List Bool → List State
  | [], _ => []
  | q :: qs, xs => sectionState q (run qs xs) :: sections qs xs

theorem sections_length (w : List State) (xs : List Bool) :
    (sections w xs).length = w.length := by
  induction w with
  | nil => rfl
  | cons q qs ih => simp only [sections, List.length_cons, ih]

theorem act_append (q : State) (xs ys : List Bool) :
    act q (xs ++ ys) = act q xs ++ act (sectionState q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append, act, sectionState, ih]

theorem run_append_input (w : List State) (xs ys : List Bool) :
    run w (xs ++ ys) = run w xs ++ run (sections w xs) ys := by
  induction w generalizing xs ys with
  | nil => rfl
  | cons q qs ih =>
    simp only [run, sections]
    rw [ih, act_append]

theorem sections_append (u v : List State) (xs : List Bool) :
    sections (u ++ v) xs = sections u (run v xs) ++ sections v xs := by
  induction u generalizing xs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.cons_append, sections, run_append, ih]

theorem cancel_prefix {α : Type} (xs ys zs : List α) :
    xs ++ ys = xs ++ zs → ys = zs := by
  induction xs with
  | nil => intro h; exact h
  | cons q qs ih =>
    intro h
    apply ih
    exact congrArg List.tail h

theorem sections_equivalent (u v : List State) (h : Equivalent u v)
    (xs : List Bool) : Equivalent (sections u xs) (sections v xs) := by
  intro ys
  have he := h (xs ++ ys)
  rw [run_append_input, run_append_input, h xs] at he
  exact cancel_prefix _ _ _ he

def reset (x y : Bool) : State := if y then C else if x then B else A

/-- Every two-bit input resets the memory, independently of its initial state. -/
theorem two_bit_reset (q : State) (x y : Bool) :
    sectionState q [x,y] = reset x y := by
  cases q <;> cases x <;> cases y <;> rfl

theorem reset_zero (q : State) : sectionState q [false,false] = A := by
  cases q <;> rfl

/-- The modified reset functions distinguish the three states already at 00. -/
theorem reset_after_output (p q : State) :
    sectionState p (act q [false,false]) = q := by
  cases p <;> cases q <;> rfl

theorem sections_snoc_zero (u : List State) (q : State) :
    sections (u ++ [q]) [false,false] =
      sections u (act q [false,false]) ++ [A] := by
  rw [sections_append]
  simp only [run, sections, reset_zero]

theorem snoc_exists : ∀ (xs : List State), xs ≠ [] →
    ∃ u q, xs = u ++ [q] := by
  intro xs
  induction xs with
  | nil => intro h; exact False.elim (h rfl)
  | cons q qs ih =>
    intro _
    cases qs with
    | nil => exact ⟨[], q, rfl⟩
    | cons r rs =>
      obtain ⟨u, s, hu⟩ := ih (by simp)
      exact ⟨q :: u, s, by simp only [List.cons_append, hu]⟩

def lastFrom (d : State) : List State → State
  | [] => d
  | q :: qs => lastFrom q qs

def lastState (xs : List State) : State := lastFrom A xs

theorem lastFrom_append_single (d : State) (xs : List State) (q : State) :
    lastFrom d (xs ++ [q]) = q := by
  induction xs generalizing d with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append, lastFrom, ih]

theorem section_last (u : List State) (hu : u ≠ []) (q : State) :
    lastState (sections u (act q [false,false])) = q := by
  obtain ⟨v, p, rfl⟩ := snoc_exists u hu
  rw [sections_append]
  simp only [sections, run, reset_after_output, lastState, lastFrom_append_single]

theorem nil_of_length_zero (xs : List State) (h : xs.length = 0) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons q qs => simp at h

/-- Reset/cancellation induction, including the empty and one-state cases. -/
theorem same_length_faithful : ∀ n (u v : List State),
    u.length = n → v.length = n → Equivalent u v → u = v := by
  intro n
  induction n with
  | zero =>
    intro u v hu hv _
    have hu0 : u = [] := nil_of_length_zero u hu
    have hv0 : v = [] := nil_of_length_zero v hv
    rw [hu0, hv0]
  | succ n ih =>
    intro u v hu hv h
    obtain ⟨U, q, rfl⟩ := snoc_exists u (by intro hz; rw [hz] at hu; simp at hu)
    obtain ⟨V, r, rfl⟩ := snoc_exists v (by intro hz; rw [hz] at hv; simp at hv)
    have hU : U.length = n := by simpa using hu
    have hV : V.length = n := by simpa using hv
    cases n with
    | zero =>
      have hU0 : U = [] := nil_of_length_zero U hU
      have hV0 : V = [] := nil_of_length_zero V hV
      subst U
      subst V
      have hz := h [false,false]
      cases q <;> cases r <;> simp_all [run, act, flip, next]
    | succ k =>
      have hUn : U ≠ [] := by intro hz; rw [hz] at hU; simp at hU
      have hVn : V ≠ [] := by intro hz; rw [hz] at hV; simp at hV
      have hs : Equivalent
          (sections U (act q [false,false]) ++ [A])
          (sections V (act r [false,false]) ++ [A]) := by
        simpa only [sections_snoc_zero] using
          sections_equivalent (U ++ [q]) (V ++ [r]) h [false,false]
      have hsec := cancel_right _ _ A hs
      have hw := ih _ _ ((sections_length _ _).trans hU)
        ((sections_length _ _).trans hV) hsec
      have hqr : q = r := by
        have he := congrArg lastState hw
        simpa only [section_last U hUn q, section_last V hVn r] using he
      subst r
      exact congrArg (fun w => w ++ [q]) (ih U V hU hV (cancel_right U V q h))

def pick : List State → Nat → State
  | [], _ => A
  | q :: _, 0 => q
  | _ :: qs, i+1 => pick qs i

theorem pick_middle (u v : List State) (q : State) :
    pick (u ++ q :: v) u.length = q := by
  induction u with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append, List.length_cons, pick, ih]

theorem pick_append_lt (u v : List State) (i : Nat) (hi : i < u.length) :
    pick (u ++ v) i = pick u i := by
  induction u generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.cons_append, pick]
      exact ih i (by simpa using hi)

theorem separator_not_lt (u v : List State)
    (h : ∀ q : State, u ++ [q] ++ v = v ++ [q] ++ u) :
    ¬ u.length < v.length := by
  intro hlt
  have ha := congrArg (fun xs => pick xs u.length) (h A)
  have hb := congrArg (fun xs => pick xs u.length) (h B)
  simp only [List.append_assoc, List.singleton_append, pick_middle,
    pick_append_lt v _ _ hlt] at ha hb
  have bad : A = B := ha.trans hb.symm
  cases bad

/-- Equality on all finite inputs determines the complete positive state word. -/
theorem positive_word_faithful (u v : List State) (h : Equivalent u v) : u = v := by
  have hsep : ∀ q : State, u ++ [q] ++ v = v ++ [q] ++ u := by
    intro q
    apply same_length_faithful ((u ++ [q] ++ v).length)
    · rfl
    · simp only [List.length_append, List.length_singleton]
      omega
    · intro xs
      simp only [run_append, run]
      rw [h xs, h (act q (run v xs))]
  have hnot := separator_not_lt u v hsep
  have hnot' := separator_not_lt v u (fun q => (hsep q).symm)
  have hlen : v.length = u.length := by omega
  exact same_length_faithful u.length u v rfl hlen h

theorem positive_word_freeness (u v : List State) : Equivalent u v ↔ u = v := by
  constructor
  · exact positive_word_faithful u v
  · intro h
    subst v
    intro xs
    rfl

end Rule30PositiveAutomaton
