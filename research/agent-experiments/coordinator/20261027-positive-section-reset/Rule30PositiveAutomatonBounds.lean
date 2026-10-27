import Ruliology.CellularAutomata.Rule30Prize
import Rule30PositiveAutomaton

/-! A linear distinguishing-input bound for positive words in the three
Rule30 states. This strengthens the finite-word reset/cancellation proof;
it is not a bound for separation of observed Rule30 column traces. -/

namespace Rule30PositiveAutomatonBounds

open Rule30PositiveAutomaton
open Rule30PositiveAutomaton.State

def AgreeUpTo (u v : List State) (n : Nat) : Prop :=
  ∀ xs : List Bool, xs.length ≤ n → run u xs = run v xs

theorem act_length (q : State) (xs : List Bool) : (act q xs).length = xs.length := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [act, List.length_cons, ih]

theorem undo_length (q : State) (xs : List Bool) : (undo q xs).length = xs.length := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [undo, List.length_cons, ih]

theorem run_length (w : List State) (xs : List Bool) : (run w xs).length = xs.length := by
  induction w with
  | nil => rfl
  | cons q qs ih => simp only [run, act_length, ih]

theorem cancel_right_upto (u v : List State) (q : State) (n : Nat)
    (h : AgreeUpTo (u ++ [q]) (v ++ [q]) n) : AgreeUpTo u v n := by
  intro xs hx
  have he := h (undo q xs) (by simpa only [undo_length] using hx)
  simpa only [run_append, run, act_undo] using he

theorem sections_upto (u v : List State) (xs : List Bool) (n : Nat)
    (h : AgreeUpTo u v (xs.length+n)) : AgreeUpTo (sections u xs) (sections v xs) n := by
  intro ys hy
  have he := h (xs ++ ys) (by simp only [List.length_append]; omega)
  have hx := h xs (by omega)
  rw [run_append_input, run_append_input, hx] at he
  exact cancel_prefix _ _ _ he

/-- Equality through twice the number of factors determines a positive word. -/
theorem faithful_upto : ∀ n (u v : List State),
    u.length=n → v.length=n → AgreeUpTo u v (2*n) → u=v := by
  intro n
  induction n with
  | zero =>
    intro u v hu hv _
    rw [nil_of_length_zero u hu, nil_of_length_zero v hv]
  | succ n ih =>
    intro u v hu hv h
    obtain ⟨U,q,rfl⟩ := snoc_exists u (by intro hz; rw [hz] at hu; simp at hu)
    obtain ⟨V,r,rfl⟩ := snoc_exists v (by intro hz; rw [hz] at hv; simp at hv)
    have hU : U.length=n := by simpa using hu
    have hV : V.length=n := by simpa using hv
    cases n with
    | zero =>
      have hU0 := nil_of_length_zero U hU
      have hV0 := nil_of_length_zero V hV
      subst U
      subst V
      have hz := h [false,false] (by decide)
      cases q <;> cases r <;> simp_all [run, act, Rule30PositiveAutomaton.flip, next]
    | succ k =>
      have hUn : U≠[] := by intro hz; rw [hz] at hU; simp at hU
      have hVn : V≠[] := by intro hz; rw [hz] at hV; simp at hV
      have hbudget : AgreeUpTo (U++[q]) (V++[r])
          ([false,false].length + 2*(k+1)) := by
        intro xs hx
        apply h xs
        simp only [List.length_cons, List.length_nil] at hx
        omega
      have hs : AgreeUpTo
          (sections U (act q [false,false]) ++ [A])
          (sections V (act r [false,false]) ++ [A]) (2*(k+1)) := by
        simpa only [sections_snoc_zero] using
          sections_upto (U++[q]) (V++[r]) [false,false] (2*(k+1)) hbudget
      have hsec := cancel_right_upto _ _ A _ hs
      have hw := ih _ _ ((sections_length _ _).trans hU)
        ((sections_length _ _).trans hV) hsec
      have hqr : q=r := by
        have he := congrArg lastState hw
        simpa only [section_last U hUn q, section_last V hVn r] using he
      subst r
      have hsmall : AgreeUpTo (U++[q]) (V++[q]) (2*(k+1)) := by
        intro xs hx
        exact h xs (by omega)
      exact congrArg (fun w => w++[q])
        (ih U V hU hV (cancel_right_upto U V q _ hsmall))

theorem take_append_length (xs ys : List Bool) :
    (xs ++ ys).take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    change b :: (bs ++ ys).take bs.length = b :: bs
    rw [ih]

theorem upto_of_exact (u v : List State) (n : Nat)
    (h : ∀ xs : List Bool, xs.length=n → run u xs=run v xs) : AgreeUpTo u v n := by
  intro xs hx
  let tail := List.replicate (n-xs.length) false
  have ht : (xs ++ tail).length=n := by
    simp only [List.length_append, List.length_replicate, tail]
    omega
  have he := h (xs ++ tail) ht
  rw [run_append_input, run_append_input] at he
  have hp := congrArg (fun ys : List Bool => ys.take xs.length) he
  have hpu : (run u xs ++ run (sections u xs) tail).take xs.length = run u xs := by
    rw [← run_length u xs]
    exact take_append_length _ _
  have hpv : (run v xs ++ run (sections v xs) tail).take xs.length = run v xs := by
    rw [← run_length v xs]
    exact take_append_length _ _
  rw [hpu,hpv] at hp
  exact hp

/-- All 2n-bit inputs suffice, uniformly in the positive composition length n. -/
theorem faithful_at_twice_length (n : Nat) (u v : List State)
    (hu : u.length=n) (hv : v.length=n)
    (h : ∀ xs : List Bool, xs.length=2*n → run u xs=run v xs) : u=v :=
  faithful_upto n u v hu hv (upto_of_exact u v (2*n) h)

theorem distinguishing_input (n : Nat) (u v : List State)
    (hu : u.length=n) (hv : v.length=n) (hne : u≠v) :
    ∃ xs : List Bool, xs.length=2*n ∧ run u xs≠run v xs := by
  apply Classical.byContradiction
  intro hn
  apply hne
  apply faithful_at_twice_length n u v hu hv
  intro xs hx
  apply Classical.byContradiction
  intro he
  exact hn ⟨xs,hx,he⟩

end Rule30PositiveAutomatonBounds
