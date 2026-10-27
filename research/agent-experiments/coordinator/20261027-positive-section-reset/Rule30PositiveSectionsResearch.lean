import Ruliology.CellularAutomata.Rule30Prize
import Rule30PositiveAutomatonBounds

/-!
Uniform common sections and injectivity at a root-flipping return birth.
These use the existing literal older-first Rule30 automaton. Products act
right to left and sections are indexed by input. No least-clock, white-orbit
observability, plateau cancellation, or prize theorem is asserted here.
-/

namespace Rule30PositiveSectionsResearch

open Rule30PositiveAutomaton Rule30PositiveAutomatonBounds
open Rule30PositiveAutomaton.State

theorem sectionState_append (q : State) (xs ys : List Bool) :
    sectionState q (xs ++ ys) = sectionState (sectionState q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append, sectionState, ih]

theorem sectionState_two_tail (q : State) (x y : Bool) (zs : List Bool) :
    sectionState q (x :: y :: zs) = sectionState (reset x y) zs := by
  change sectionState q ([x,y] ++ zs) = _
  rw [sectionState_append, two_bit_reset]

theorem act_drop_two (q r : State) (xs : List Bool) :
    (act q xs).drop 2 = (act r xs).drop 2 := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y zs =>
      change act (sectionState q [x,y]) zs = act (sectionState r [x,y]) zs
      rw [two_bit_reset, two_bit_reset]

theorem act_drop_agree (n : Nat) (q r : State) (xs ys : List Bool)
    (hlen : xs.length = ys.length) (h : xs.drop n = ys.drop n) :
    (act q xs).drop (n+2) = (act r ys).drop (n+2) := by
  induction n generalizing q r xs ys with
  | zero =>
    simp only [List.drop_zero] at h
    subst ys
    exact act_drop_two q r xs
  | succ n ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlen
    | cons x xs =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
        have hl : xs.length = ys.length := Nat.succ.inj hlen
        have hh : xs.drop n = ys.drop n := by simpa only [List.drop_succ_cons] using h
        simpa only [act, List.drop_succ_cons, Nat.add_assoc] using
          ih (next q x) (next r y) xs ys hl hh

/-- After twice the composition length, equal-length positive scans have
identical output tails on every common input. -/
theorem run_drop_common (n : Nat) (u v : List State)
    (hu : u.length=n) (hv : v.length=n) (xs : List Bool) :
    (run u xs).drop (2*n) = (run v xs).drop (2*n) := by
  induction n generalizing u v with
  | zero =>
    rw [nil_of_length_zero u hu, nil_of_length_zero v hv]
  | succ n ih =>
    cases u with
    | nil => simp at hu
    | cons q us =>
      cases v with
      | nil => simp at hv
      | cons r vs =>
        have hu' : us.length=n := Nat.succ.inj hu
        have hv' : vs.length=n := Nat.succ.inj hv
        have hh := act_drop_agree (2*n) q r (run us xs) (run vs xs)
          (by rw [run_length, run_length]) (ih us vs hu' hv')
        simpa only [run, Nat.mul_succ] using hh

theorem sectionState_common_tail (n : Nat) (q r : State) (xs ys : List Bool)
    (hlen : xs.length=ys.length) (hsize : n+2≤xs.length)
    (h : xs.drop n=ys.drop n) : sectionState q xs=sectionState r ys := by
  induction n generalizing q r xs ys with
  | zero =>
    simp only [List.drop_zero] at h
    subst ys
    cases xs with
    | nil => simp at hsize
    | cons x xs =>
      cases xs with
      | nil => simp at hsize
      | cons y zs => rw [sectionState_two_tail, sectionState_two_tail]
  | succ n ih =>
    cases xs with
    | nil => simp at hsize
    | cons x xs =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
        have hl : xs.length=ys.length := Nat.succ.inj hlen
        have hs : n+2≤xs.length := by simp only [List.length_cons] at hsize; omega
        have hh : xs.drop n=ys.drop n := by simpa only [List.drop_succ_cons] using h
        exact ih (next q x) (next r y) xs ys hl hs hh

/-- Any two positive words of length n have literally equal section words
at every input of length at least2n, independently of ancestry or clock. -/
theorem common_sections (n : Nat) (u v : List State)
    (hu : u.length=n) (hv : v.length=n) (xs : List Bool)
    (hxs : 2*n≤xs.length) : sections u xs=sections v xs := by
  induction n generalizing u v with
  | zero => rw [nil_of_length_zero u hu, nil_of_length_zero v hv]
  | succ n ih =>
    cases u with
    | nil => simp at hu
    | cons q us =>
      cases v with
      | nil => simp at hv
      | cons r vs =>
        have hu' : us.length=n := Nat.succ.inj hu
        have hv' : vs.length=n := Nat.succ.inj hv
        have hs : sectionState q (run us xs)=sectionState r (run vs xs) := by
          apply sectionState_common_tail (2*n)
          · rw [run_length, run_length]
          · rw [run_length]; omega
          · exact run_drop_common n us vs hu' hv' xs
        have ht := ih us vs hu' hv' (by omega)
        simp only [sections, hs, ht]

def rootFlip : List State → Bool
  | [] => false
  | q :: qs => Bool.xor (rootFlip qs) (flip q)

theorem run_nil (u : List State) : run u []=[] := by
  induction u with
  | nil => rfl
  | cons q qs ih => simp only [run, ih, act]

theorem run_singleton (u : List State) (b : Bool) :
    run u [b]=[Bool.xor b (rootFlip u)] := by
  induction u with
  | nil => cases b <;> rfl
  | cons q qs ih =>
    simp only [run, ih, act, rootFlip]
    rw [Bool.xor_assoc]

theorem flipping_singleton (u : List State) (h : run u [false]=[true]) (b : Bool) :
    run u [b]=[!b] := by
  have hf : rootFlip u=true := by simpa only [run_singleton, Bool.false_xor, List.singleton_inj] using h
  rw [run_singleton, hf]
  cases b <;> rfl

theorem append_split (a b c d : List State) (hlen : a.length=c.length)
    (h : a++b=c++d) : a=c ∧ b=d := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => exact ⟨rfl,h⟩
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases c with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨he,ht⟩ := h
      obtain ⟨hs,hb⟩ := ih ys (Nat.succ.inj hlen) ht
      exact ⟨by rw [he,hs],hb⟩

theorem flipping_sections_determine (u v : List State)
    (hu : run u [false]=[true]) (hv : run v [false]=[true])
    (h0 : sections u [false]=sections v [false])
    (h1 : sections u [true]=sections v [true]) : u=v := by
  apply positive_word_faithful
  intro xs
  cases xs with
  | nil => rw [run_nil, run_nil]
  | cons b bs =>
    change run u ([b]++bs)=run v ([b]++bs)
    rw [run_append_input, run_append_input, flipping_singleton u hu, flipping_singleton v hv]
    cases b
    · rw [h0]
    · rw [h1]

/-- A common root-flipping birth cannot merge equal-length positive words:
equivalence of the zero-sections of their squares forces literal equality. -/
theorem birth_sections_injective (u v : List State) (hlen : u.length=v.length)
    (hu : run u [false]=[true]) (hv : run v [false]=[true])
    (h : Equivalent (sections (u++u) [false]) (sections (v++v) [false])) : u=v := by
  have he := positive_word_faithful _ _ h
  rw [sections_append, sections_append, hu, hv] at he
  obtain ⟨h1,h0⟩ := append_split _ _ _ _
    (by simpa only [sections_length] using hlen) he
  exact flipping_sections_determine u v hu hv h0 h1

end Rule30PositiveSectionsResearch
