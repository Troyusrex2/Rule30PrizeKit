import CedarSafetyBridge

/-! Whole-word return8 is exactly return2 of the prefix after deleting
three newest cells. This contains no safety-completeness assertion. -/
namespace CedarReturnEightReduction
open CedarSafetySoundness CedarSafety
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def category (i : Fin 36) : Nat :=
  if i.val < 8 then 0 else if i.val < 12 then 1 else if i.val < 20 then 2 else 3

theorem category_le (i : Fin 36) : category i ≤ 3 := by
  unfold category
  split <;> first | omega | (split <;> first | omega | (split <;> omega))

theorem category_certificate : ∀ (i : Fin 36) (v : Bool),
    let p := (CedarSafetyBridge.state i).previous
    let r := (CedarSafetyBridge.state i).older
    let q := nextProfile p r v
    if category i = 3 then q.t8 ≠ v
    else q.t8 = v ∧ ∃ j : Fin 36,
      (CedarSafetyBridge.state j).previous = q ∧
      (CedarSafetyBridge.state j).older = p ∧
      (if category i = 0 then category j = (if q.t2 = v then 0 else 1)
       else category j = category i + 1) := by
  decide +kernel

def run2 (p r : Profile) (xs : List Bool) : List Bool :=
  change p.t1 r.t1 (change p.t0 r.t0 xs)

theorem run2_cons (p r : Profile) (v : Bool) (vs : List Bool) :
    run2 p r (v :: vs) = (nextProfile p r v).t2 :: run2 (nextProfile p r v) p vs := rfl

theorem run2_white (xs : List Bool) : run2 zero zero xs = evolution 2 xs := rfl

def ShortTwo (p r : Profile) (xs : List Bool) : Prop :=
  run2 p r (xs.take (xs.length-3)) = xs.take (xs.length-3)

theorem short_two_small (p r : Profile) (xs : List Bool) (h : xs.length ≤ 3) :
    ShortTwo p r xs := by
  have hz : xs.length-3 = 0 := by omega
  simp [ShortTwo,hz,run2,change]

theorem short_two_cons (p r : Profile) (v : Bool) (vs : List Bool) :
    ShortTwo p r (v :: vs) ↔ vs.length ≤ 2 ∨
      ((nextProfile p r v).t2 = v ∧ ShortTwo (nextProfile p r v) p vs) := by
  by_cases h : vs.length ≤ 2
  · constructor
    · intro _; exact Or.inl h
    · intro _; exact short_two_small p r (v::vs) (by simp only [List.length_cons]; omega)
  · unfold ShortTwo
    rw [show (v :: vs).length-3 = (vs.length-3)+1 by simp only [List.length_cons]; omega]
    simp only [List.take_succ_cons,run2_cons,List.cons.injEq,h,false_or]

theorem dispatch (xs : List Bool) : ∀ i : Fin 36,
    run8 (CedarSafetyBridge.state i).previous (CedarSafetyBridge.state i).older xs = xs ↔
      if category i = 0 then
        ShortTwo (CedarSafetyBridge.state i).previous (CedarSafetyBridge.state i).older xs
      else xs.length + category i ≤ 3 := by
  induction xs with
  | nil =>
    intro i
    simp only [run8_nil,List.length_nil,Nat.zero_add,true_iff]
    by_cases h : category i = 0
    · rw [if_pos h]
      exact short_two_small _ _ [] (by simp)
    · rw [if_neg h]
      exact category_le i
  | cons v vs ih =>
    intro i
    let p := (CedarSafetyBridge.state i).previous
    let r := (CedarSafetyBridge.state i).older
    have cert := category_certificate i v
    change (if category i = 3 then (nextProfile p r v).t8 ≠ v else
      (nextProfile p r v).t8 = v ∧ ∃ j : Fin 36,
        (CedarSafetyBridge.state j).previous = nextProfile p r v ∧
        (CedarSafetyBridge.state j).older = p ∧
        (if category i = 0 then category j = (if (nextProfile p r v).t2 = v then 0 else 1)
         else category j = category i+1)) at cert
    change run8 p r (v::vs) = v::vs ↔
      if category i = 0 then ShortTwo p r (v::vs) else (v::vs).length+category i ≤ 3
    by_cases h3 : category i = 3
    · simp only [h3,if_true] at cert
      simp [run8_cons,List.cons.injEq,cert,h3]
    · simp only [h3,if_false] at cert
      obtain ⟨h8,j,hp,hr,hcat⟩ := cert
      have sub := ih j
      rw [hp,hr] at sub
      rw [run8_cons,h8,List.cons.injEq]
      simp only [true_and]
      rw [sub]
      by_cases h0 : category i = 0
      · simp only [h0,if_true] at hcat ⊢
        by_cases h2 : (nextProfile p r v).t2 = v
        · have hj : category j = 0 := by simpa only [h2,if_true] using hcat
          rw [hj]
          simp only [if_true]
          rw [short_two_cons]
          simp only [h2,true_and]
          constructor
          · intro h; exact Or.inr h
          · intro h
            rcases h with hs | hs
            · exact short_two_small _ _ vs (by omega)
            · exact hs
        · have hj : category j = 1 := by simpa only [h2,if_false] using hcat
          rw [hj]
          simp only [show ¬ (1:Nat)=0 by decide,if_false,short_two_cons,h2,false_and,or_false]
          omega
      · simp only [h0,if_false] at hcat ⊢
        have hj : category j ≠ 0 := by omega
        simp only [hj,if_false,List.length_cons]
        omega

/-- Exact all-width finite-white reduction. Empty and short prefixes are
handled by Nat subtraction and the literal empty-word evolution. -/
theorem return_eight_iff_prefix_two (xs : List Bool) :
    evolution 8 xs = xs ↔
      evolution 2 (xs.take (xs.length-3)) = xs.take (xs.length-3) := by
  have h := dispatch xs ⟨0,by decide⟩
  change run8 zero zero xs = xs ↔ ShortTwo zero zero xs at h
  simpa only [run8_white,ShortTwo,run2_white] using h

end CedarReturnEightReduction
