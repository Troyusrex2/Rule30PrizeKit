import Rule30NormalizationStreamResearch

/-! Physical bit streams for arbitrary finite integer rows. This module connects
the checked machine to Phi, but does not yet identify its accepted relation with
the numerical normalizer, nor prove infinite-trace completeness. -/

namespace Rule30NormalizationMachineResearch

def centerCode (c n : Nat) : Nat := if n ≤ c then 0 else min 4 (n-c)

theorem centerCode_zero (c : Nat) : centerCode c 0 = 0 := by simp [centerCode]

theorem centerCode_succ (c n : Nat) :
    nextCode (centerCode c n) (decide (n = c)) = centerCode c (n+1) := by
  by_cases he : n = c
  · subst n
    simp [nextCode, centerCode]
  · by_cases hl : n < c
    · have hn : n ≤ c := by omega
      have hs : n+1 ≤ c := by omega
      simp [nextCode, centerCode, he, hn, hs]
    · have hn : ¬ n ≤ c := by omega
      have hs : ¬ n+1 ≤ c := by omega
      have hp : 0 < min 4 (n-c) := by omega
      simp only [nextCode, he, decide_false, Bool.false_eq_true, ↓reduceIte,
        centerCode, hn, hs]
      have hz : (min 4 (n-c) == 0) = false := by simp; omega
      rw [hz]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

theorem centerCode_marker (c n : Nat) :
    (decide (n = c) && centerCode c n != 0) = false := by
  by_cases he : n = c
  · subst n; simp [centerCode]
  · simp [he]

theorem centerCode_one (c n : Nat) : centerCode c (n+1) = 1 ↔ n = c := by
  unfold centerCode
  split <;> omega

theorem centerCode_two (c n : Nat) : centerCode c (n+1) = 2 ↔ n = c+1 := by
  unfold centerCode
  split <;> omega

theorem centerCode_allow (c n t : Nat) (ht : t < 3) :
    (centerCode c (n+1) == 0 || centerCode c (n+1) ≤ t+1) = decide (n ≤ c+t) := by
  unfold centerCode
  split
  · simp only [Nat.reduceBEq, Bool.true_or]
    have h : n ≤ c+t := by omega
    simp [h]
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    omega

def relationRun (a b c : Nat) : Nat → Nat
  | 0 => 4
  | n+1 => relStep (relationRun a b c n) (a.testBit n) (b.testBit n) (decide (n ≤ c))

def actualView (a b c n : Nat) : View :=
  ⟨relationRun a b c n, relationRun (Phi a) (Phi b) (c+1) n,
    relationRun (Phi (Phi a)) (Phi (Phi b)) (c+2) n,
    history a n, history b n, centerCode c n⟩

def actualLetter (a b c n : Nat) : Letter :=
  ⟨a.testBit n, b.testBit n, decide (n = c)⟩

theorem actualView_zero (a b c : Nat) : actualView a b c 0 = initialView := by
  simp [actualView, relationRun, history_zero, centerCode_zero, initialView]

theorem actualView_advance (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    (actualView a b c n).advance (a.testBit n) (b.testBit n) (decide (n = c)) =
      some (actualView a b c (n+1)) := by
  have g0 : (centerCode c (n+1) == 1 && a.testBit n != b.testBit n) = false := by
    by_cases hc : centerCode c (n+1) = 1
    · have hn := (centerCode_one c n).mp hc
      subst n
      simp [h0]
    · simp [hc]
  have g1 : (centerCode c (n+1) == 2 &&
      (Phi a).testBit n != (Phi b).testBit n) = false := by
    by_cases hc : centerCode c (n+1) = 2
    · have hn := (centerCode_two c n).mp hc
      subst n
      simp [h1]
    · simp [hc]
  simp only [View.advance, actualView, centerCode_marker, Bool.false_eq_true,
    ↓reduceIte, centerCode_succ, ← first_exact, g0, g1, Bool.false_or,
    ← second_exact, centerCode_allow c n 0 (by decide),
    centerCode_allow c n 1 (by decide), centerCode_allow c n 2 (by decide),
    Nat.add_zero, history_succ, relationRun]

def actualInput (a b c : Nat) (n : Nat) : List Letter :=
  (List.range n).map (actualLetter a b c)

theorem View.run_append (v : View) (xs ys : List Letter) :
    v.run (xs ++ ys) = (v.run xs).bind (fun w => w.run ys) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, View.run]
      cases h : v.advance x.a x.b x.marker with
      | none => rfl
      | some w => simpa only [Option.bind_some] using ih w

theorem actualInput_run (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    initialView.run (actualInput a b c n) = some (actualView a b c n) := by
  induction n with
  | zero => simp [actualInput, View.run, actualView_zero]
  | succ n ih =>
      simp only [actualInput, List.range_succ, List.map_append, List.map_singleton,
        View.run_append] at *
      rw [ih]
      simp only [Option.bind_some, View.run, actualLetter]
      rw [actualView_advance a b c n h0 h1]
      rfl

/-- The checked end condition applies to actual rows of every integer size,
provided the two relevant center observations agree. This does not yet state
the corresponding normalization implication. -/
theorem actual_input_safe (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    endGood (actualView a b c n).encode = true :=
  safe_after_input _ (actualInput_run a b c n h0 h1)

end Rule30NormalizationMachineResearch
