import Rule30NormalizationRelationResearch

/-! An all-integer implication for the common-cut relation recognized by the
machine. TailLanguageResearch supplies the stripe-language interpretation.
This is not the numerical-normalization theorem or an infinite-trace theorem. -/

namespace Rule30NormalizationMachineResearch

def ZerosFrom (a n : Nat) : Prop := ∀ i, n ≤ i → a.testBit i = false

theorem ZerosFrom.mono {a n m : Nat} (h : ZerosFrom a n) (hn : n ≤ m) : ZerosFrom a m :=
  fun i hi => h i (by omega)

theorem zerosFrom_large (a n : Nat) (ha : a ≤ n) : ZerosFrom a n := by
  intro i hi
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_le_of_lt (by omega) Nat.lt_two_pow_self

theorem ZerosFrom.phi {a n : Nat} (h : ZerosFrom a n) : ZerosFrom (Phi a) (n+2) := by
  intro i hi
  rw [Phi_testBit, before_of_lt a i 0 (by omega), before_of_lt a i 1 (by omega)]
  simp only [h i (by omega), h (i-(0+1)) (by omega), h (i-(1+1)) (by omega)]
  rfl

theorem relationRun_lt (a b c n : Nat) : relationRun a b c n < 200 := by
  cases n with
  | zero => simp [relationRun]
  | succ n => exact relStep_lt _ _ _ _

theorem actualView_valid (a b c n : Nat) : (actualView a b c n).Valid := by
  refine ⟨relationRun_lt _ _ _ _, relationRun_lt _ _ _ _, relationRun_lt _ _ _ _,
    history_lt _ _, history_lt _ _, ?_⟩
  change centerCode c n ≤ 4
  unfold centerCode
  split <;> omega

theorem relAccept_mod (e : Nat) : relAccept (e % 256) = relAccept e := by
  change relAccept (e % 2^8) = relAccept e
  simp only [relAccept, Nat.testBit_mod_two_pow, Nat.reduceLT, decide_true, Bool.true_and]

theorem View.accept_encode (v : View) (hv : v.Valid) :
    accept v.encode 0 = relAccept v.e0 ∧ accept v.encode 1 = relAccept v.e1 ∧
    accept v.encode 2 = relAccept v.e2 := by
  obtain ⟨h0,h1,h2,_,_,_⟩ := v.decode_encode hv
  have a0 := congrArg relAccept h0
  have a1 := congrArg relAccept h1
  have a2 := congrArg relAccept h2
  simp only [relAccept_mod] at a0 a1 a2
  exact ⟨a0,a1,a2⟩

theorem step_actual_zero (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (ha : a.testBit n = false) (hb : b.testBit n = false) (hc : n ≠ c) :
    step (actualView a b c n).encode 0 = some (actualView a b c (n+1)).encode := by
  have h := (actualView a b c n).encode_advance (actualView_valid a b c n)
    (a.testBit n) (b.testBit n) (decide (n = c))
  rw [actualView_advance a b c n h0 h1] at h
  simpa only [ha,hb,hc,decide_false,symbol,Bool.toNat_false,Nat.mul_zero,
    Nat.add_zero,Option.map_some] using h

theorem flush_actual (a b c n k : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (ha : ZerosFrom a n) (hb : ZerosFrom b n) (hc : c < n) :
    flush k (actualView a b c n).encode = some (actualView a b c (n+k)).encode := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [flush, step_actual_zero a b c n h0 h1 (ha n (by omega)) (hb n (by omega)) (by omega)]
      simp only [Option.bind_some]
      have h := ih (n+1) (ha.mono (by omega)) (hb.mono (by omega)) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h

def RowRelated (a b c : Nat) : Prop := a = b ∨ ∃ j, EligibleCut a b c j ∧
  a.testBit (j+1) = false ∧ b.testBit (j+1) = false ∧
  ∀ i, j+1 < i → a.testBit i = b.testBit i

theorem prefixEq_eq {a b n : Nat} (ha : ZerosFrom a n) (hb : ZerosFrom b n)
    (h : PrefixEq a b n) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact h i hi
  · rw [ha i (by omega), hb i (by omega)]

theorem relationRun_full_iff (a b c n : Nat) (ha : ZerosFrom a n) (hb : ZerosFrom b n)
    (hc : c+1 < n) : relAccept (relationRun a b c n) = true ↔ RowRelated a b c := by
  rw [relationRun_accept_iff]
  constructor
  · rintro (he | ⟨j,hj,he,hza,hzb,hs⟩)
    · exact Or.inl (prefixEq_eq ha hb he)
    · right
      refine ⟨j,he,hza,hzb,?_⟩
      intro i hi
      by_cases hin : i < n
      · exact hs i hi hin
      · rw [ha i (by omega), hb i (by omega)]
  · rintro (he | ⟨j,he,hza,hzb,hs⟩)
    · left
      subst b
      intro i hi
      rfl
    · exact Or.inr ⟨j,by have hj := he.1; omega,he,hza,hzb,fun i hi _ => hs i hi⟩

/-- No pair of finite rows can first acquire the common-cut relation after
two steps if its two preceding center observations agree. The common-cut
relation's stripe language is interpreted in TailLanguageResearch;
numerical-normalizer equivalence remains open. -/
theorem two_step_common_cut (a b c : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (h2 : RowRelated (Phi (Phi a)) (Phi (Phi b)) (c+2)) :
    RowRelated a b c ∨ RowRelated (Phi a) (Phi b) (c+1) := by
  let n := a+b+c+1
  have ha : ZerosFrom a n := zerosFrom_large a n (by dsimp [n]; omega)
  have hb : ZerosFrom b n := zerosFrom_large b n (by dsimp [n]; omega)
  have hc : c < n := by dsimp [n]; omega
  have hp : (n+2)+2 ≤ n+5 := by omega
  have ha2 := ha.phi.phi.mono hp
  have hb2 := hb.phi.phi.mono hp
  have r2 := (relationRun_full_iff (Phi (Phi a)) (Phi (Phi b)) (c+2) (n+5)
    ha2 hb2 (by omega)).mpr h2
  have hgood := actual_input_safe a b c n h0 h1
  have hcode : (actualView a b c n).encode >>> 32 ≠ 0 := by
    have hdec := (actualView a b c n).decode_encode (actualView_valid a b c n)
    rw [hdec.2.2.2.2.2]
    change centerCode c n ≠ 0
    unfold centerCode
    split <;> omega
  simp only [endGood, hcode, beq_iff_eq, ↓reduceIte,
    flush_actual a b c n 5 h0 h1 ha hb hc] at hgood
  obtain ⟨ac0,ac1,ac2⟩ := (actualView a b c (n+5)).accept_encode
    (actualView_valid a b c (n+5))
  rw [ac0,ac1,ac2] at hgood
  change (!(relAccept (relationRun (Phi (Phi a)) (Phi (Phi b)) (c+2) (n+5)) &&
    !relAccept (relationRun a b c (n+5)) &&
    !relAccept (relationRun (Phi a) (Phi b) (c+1) (n+5)))) = true at hgood
  rw [r2] at hgood
  have hor : relAccept (relationRun a b c (n+5)) = true ∨
      relAccept (relationRun (Phi a) (Phi b) (c+1) (n+5)) = true := by
    cases hx : relAccept (relationRun a b c (n+5)) <;>
      cases hy : relAccept (relationRun (Phi a) (Phi b) (c+1) (n+5)) <;>
      simp_all
  rcases hor with he | he
  · exact Or.inl ((relationRun_full_iff a b c (n+5) (ha.mono (by omega))
      (hb.mono (by omega)) (by omega)).mp he)
  · exact Or.inr ((relationRun_full_iff (Phi a) (Phi b) (c+1) (n+5)
      (ha.phi.mono (by omega)) (hb.phi.mono (by omega)) (by omega)).mp he)

end Rule30NormalizationMachineResearch
