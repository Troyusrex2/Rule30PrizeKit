import Rule30NormalizationActualInputResearch

/-! Parser semantics in terms of a common cut and equality above that cut.
TailLanguageResearch identifies the tail DFA with the stripe language.
Numerical-normalizer equivalence and infinite-trace completeness remain open. -/

namespace Rule30NormalizationMachineResearch

def relCode (ta tb : Nat) (ident pending valid : Bool) : Nat :=
  8 * (5 * ta + tb) + 4 * ident.toNat + 2 * pending.toNat + valid.toNat

theorem relCode_decode (ta tb : Nat) (ht : tb < 5) (ident pending valid : Bool) :
    (relCode ta tb ident pending valid / 8) / 5 = ta ∧
    (relCode ta tb ident pending valid / 8) % 5 = tb ∧
    (relCode ta tb ident pending valid).testBit 0 = valid ∧
    (relCode ta tb ident pending valid).testBit 1 = pending ∧
    (relCode ta tb ident pending valid).testBit 2 = ident := by
  cases ident <;> cases pending <;> cases valid <;>
    simp [relCode, Nat.testBit_eq_decide_div_mod_eq] <;> omega

def tailRun (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => tailNext (tailRun a n) (a.testBit n)

theorem tailRun_lt (a n : Nat) : tailRun a n < 5 := by
  cases n with
  | zero => simp [tailRun]
  | succ n => exact tailNext_lt _ _

def identAt (a b : Nat) : Nat → Bool
  | 0 => true
  | n+1 => identAt a b n && (a.testBit n == b.testBit n)

def pendingAt (a b c : Nat) : Nat → Bool
  | 0 => false
  | n+1 => decide (n ≤ c) && a.testBit n && b.testBit n &&
      (tailRun a (n+1) == 1 || tailRun a (n+1) == 3) &&
      (tailRun b (n+1) == 1 || tailRun b (n+1) == 3)

def validAt (a b c : Nat) : Nat → Bool
  | 0 => false
  | n+1 => (validAt a b c n && (a.testBit n == b.testBit n)) ||
      (pendingAt a b c n && !a.testBit n && !b.testBit n)

theorem relationRun_code (a b c n : Nat) :
    relationRun a b c n = relCode (tailRun a n) (tailRun b n)
      (identAt a b n) (pendingAt a b c n) (validAt a b c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      obtain ⟨hta,htb,hv,hp,hi⟩ := relCode_decode (tailRun a n) (tailRun b n)
        (tailRun_lt b n) (identAt a b n) (pendingAt a b c n) (validAt a b c n)
      rw [relationRun, ih]
      simp only [relStep, hta, htb, hv, hp, hi]
      rfl

def PrefixEq (a b n : Nat) : Prop := ∀ i, i < n → a.testBit i = b.testBit i

theorem identAt_iff (a b n : Nat) : identAt a b n = true ↔ PrefixEq a b n := by
  induction n with
  | zero => simp [identAt, PrefixEq]
  | succ n ih =>
      simp only [identAt, Bool.and_eq_true, beq_iff_eq, ih]
      constructor
      · rintro ⟨h,he⟩ i hi
        by_cases hin : i < n
        · exact h i hin
        · have hn : i = n := by omega
          simpa [hn] using he
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

def EligibleCut (a b c j : Nat) : Prop :=
  j ≤ c ∧ a.testBit j = true ∧ b.testBit j = true ∧
    (tailRun a (j+1) = 1 ∨ tailRun a (j+1) = 3) ∧
    (tailRun b (j+1) = 1 ∨ tailRun b (j+1) = 3)

theorem pendingAt_iff (a b c n : Nat) : pendingAt a b c n = true ↔
    ∃ j, n = j+1 ∧ EligibleCut a b c j := by
  cases n with
  | zero => simp [pendingAt]
  | succ n => simp [pendingAt, EligibleCut, and_assoc]

def CutWitness (a b c n : Nat) : Prop := ∃ j, j+1 < n ∧ EligibleCut a b c j ∧
  a.testBit (j+1) = false ∧ b.testBit (j+1) = false ∧
  ∀ i, j+1 < i → i < n → a.testBit i = b.testBit i

theorem cutWitness_succ (a b c n : Nat) : CutWitness a b c (n+1) ↔
    (CutWitness a b c n ∧ a.testBit n = b.testBit n) ∨
    (pendingAt a b c n = true ∧ a.testBit n = false ∧ b.testBit n = false) := by
  constructor
  · rintro ⟨j,hj,he,hza,hzb,hs⟩
    by_cases hjn : j+1 < n
    · left
      exact ⟨⟨j,hjn,he,hza,hzb,fun i hi hn => hs i hi (by omega)⟩,
        hs n hjn (by omega)⟩
    · have hn : n = j+1 := by omega
      right
      exact ⟨(pendingAt_iff a b c n).mpr ⟨j,hn,he⟩, hn ▸ hza, hn ▸ hzb⟩
  · rintro (⟨⟨j,hj,he,hza,hzb,hs⟩,hn⟩ | ⟨hp,hza,hzb⟩)
    · refine ⟨j,by omega,he,hza,hzb,?_⟩
      intro i hi hin
      by_cases hh : i < n
      · exact hs i hi hh
      · have hi : i = n := by omega
        simpa [hi] using hn
    · obtain ⟨j,hn,he⟩ := (pendingAt_iff a b c n).mp hp
      refine ⟨j,by omega,he,?_,?_,?_⟩
      · simpa only [hn] using hza
      · simpa only [hn] using hzb
      · intro i hi hin
        omega

theorem validAt_iff (a b c n : Nat) : validAt a b c n = true ↔ CutWitness a b c n := by
  induction n with
  | zero => simp [validAt, CutWitness]
  | succ n ih =>
      rw [cutWitness_succ]
      simp [validAt, ih, and_assoc]

def relAccept (e : Nat) : Bool := e.testBit 0 || e.testBit 2

theorem relationRun_accept_iff (a b c n : Nat) :
    relAccept (relationRun a b c n) = true ↔ PrefixEq a b n ∨ CutWitness a b c n := by
  rw [relationRun_code]
  obtain ⟨_,_,hv,_,hi⟩ := relCode_decode (tailRun a n) (tailRun b n)
    (tailRun_lt b n) (identAt a b n) (pendingAt a b c n) (validAt a b c n)
  simp only [relAccept, hv, hi, Bool.or_eq_true, identAt_iff, validAt_iff, or_comm]

end Rule30NormalizationMachineResearch
