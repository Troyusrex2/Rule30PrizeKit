import Rule30NormalizationFirstMeetingResearch

/-! Two-step preservation certificate and its actual-row semantics.
No converse completeness or full prize claim is made. -/

namespace Rule30NormalizationMachineResearch

def preservesTwo (s : Nat) : Bool :=
  if s >>> 32 == 0 then true else
  match flush 5 s with
  | none => true
  | some e => !accept e 0 || accept e 2

theorem preservesTwo_pool : allNodes pool preservesTwo = true := by decide +kernel

theorem StripeRelated.center_pair {a b c : Nat} (h : StripeRelated a b c) :
    a.testBit c = b.testBit c ∧ (Phi a).testBit (c+1) = (Phi b).testBit (c+1) := by
  rcases h with he | ⟨j,hjc,hsa,hsb,hja,hjb,hza,hzb,hs⟩
  · subst b
    exact ⟨rfl,rfl⟩
  · have hagree : ∀ i, j ≤ i → a.testBit i = b.testBit i := by
      intro i hi
      by_cases h0 : i = j
      · rw [h0,hja,hjb]
      · by_cases h1 : i = j+1
        · rw [h1,hza,hzb]
        · exact hs i (by omega)
    refine ⟨hagree c hjc,?_⟩
    by_cases hc : c = j
    · subst c
      rw [Phi_testBit, Phi_testBit, before_succ_zero, before_succ_zero,hza,hzb,hja,hjb]
      simp
    · rw [Phi_testBit, Phi_testBit, before_succ_zero, before_succ_zero,
        before_of_lt a (c+1) 1 (by omega), before_of_lt b (c+1) 1 (by omega),
        hagree (c+1) (by omega), hagree c hjc, hagree ((c+1)-(1+1)) (by omega)]

theorem preservesTwo_after_actual (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    preservesTwo (actualView a b c n).encode = true := by
  have hr : Rule30NormalizationMachineResearch.run initial
      ((actualInput a b c n).map Letter.val) = some (actualView a b c n).encode := by
    rw [← initialView_encode, initialView.run_encode initialView_valid,
      actualInput_run a b c n h0 h1]
    rfl
  apply all_of_member preservesTwo_pool (run_member initial_member ?_ hr)
  intro u hu
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hu
  exact symbol_lt x.a x.b x.marker

/-- Stripe-related rows remain stripe-related after two Rule 30 steps.
One-step preservation is false, as shown by rows 2 and 3 at center 1. -/
theorem stripe_related_preserves_two (a b c : Nat) (h : StripeRelated a b c) :
    StripeRelated (Phi (Phi a)) (Phi (Phi b)) (c+2) := by
  obtain ⟨h0,h1⟩ := h.center_pair
  let n := a+b+c+1
  have ha : ZerosFrom a n := zerosFrom_large a n (by dsimp [n]; omega)
  have hb : ZerosFrom b n := zerosFrom_large b n (by dsimp [n]; omega)
  have hc : c < n := by dsimp [n]; omega
  have he := (rowRelated_iff_stripeRelated a b c).mpr h
  have r0 := (relationRun_full_iff a b c (n+5) (ha.mono (by omega))
    (hb.mono (by omega)) (by omega)).mpr he
  have hg := preservesTwo_after_actual a b c n h0 h1
  have hcode : (actualView a b c n).encode >>> 32 ≠ 0 := by
    have hdec := (actualView a b c n).decode_encode (actualView_valid a b c n)
    rw [hdec.2.2.2.2.2]
    change centerCode c n ≠ 0
    unfold centerCode
    split <;> omega
  simp only [preservesTwo, hcode, beq_iff_eq, ↓reduceIte,
    flush_actual a b c n 5 h0 h1 ha hb hc] at hg
  obtain ⟨ac0,_,ac2⟩ := (actualView a b c (n+5)).accept_encode
    (actualView_valid a b c (n+5))
  rw [ac0,ac2] at hg
  change (!relAccept (relationRun a b c (n+5)) ||
    relAccept (relationRun (Phi (Phi a)) (Phi (Phi b)) (c+2) (n+5))) = true at hg
  rw [r0] at hg
  simp only [Bool.not_true, Bool.false_or] at hg
  apply (rowRelated_iff_stripeRelated _ _ _).mp
  apply (relationRun_full_iff _ _ _ (n+5) (ha.phi.phi.mono (by omega))
    (hb.phi.phi.mono (by omega)) (by omega)).mp
  exact hg

end Rule30NormalizationMachineResearch
