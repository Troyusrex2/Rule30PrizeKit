module
public import SeedSections

/-! One exact compression of the actual center sections. The result is a
minimum length in POSITIVE words of the three stated transformations, evaluated
on the zero stream. It is not an algorithmic complexity bound and does not
give a closed recurrence on the compressed family. -/
@[expose] public section
namespace SectionCompression
open SeedAutomaton SeedAutomaton.St SeedSections

theorem rounds_length (n : Nat) (w : List St) : (rounds n w).length=w.length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rounds,dual_length,ih]

theorem rounds_A_cons (n : Nat) (w : List St) : rounds n (A::w)=A::rounds n w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rounds,ih,dual_A_prefix]; rfl

theorem rounds_A_prefix (n k : Nat) (w : List St) :
    rounds n (List.replicate k A ++ w)=List.replicate k A ++ rounds n w := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,rounds_A_cons,ih]

theorem two_round_head (s : St) (w : List St) :
    ∃ v,rounds 2 (s::w)=A::v ∧ v.length=w.length := by
  cases s with
  | A => exact ⟨dual false (dual false w),rfl,by rw [dual_length,dual_length]⟩
  | B => exact ⟨dual false (dual true w),rfl,by rw [dual_length,dual_length]⟩
  | C => exact ⟨dual true (dual true w),rfl,by rw [dual_length,dual_length]⟩

/-- Every two dual rounds produce one more erasable leading A. -/
theorem erase_prefix (k : Nat) (w : List St) (hk : k≤w.length) :
    ∃ v,rounds (2*k) w=List.replicate k A ++ v ∧ v.length=w.length-k := by
  induction k generalizing w with
  | zero => exact ⟨w,rfl,by simp⟩
  | succ k ih =>
    cases w with
    | nil => simp at hk
    | cons s w =>
      obtain ⟨v,hv,len⟩ := two_round_head s w
      obtain ⟨u,hu,lenu⟩ := ih v (by simp only [List.length_cons] at hk; omega)
      refine ⟨u,?_,?_⟩
      · rw [show 2*(k+1)=2+2*k by omega,rounds_add,hv,rounds_A_cons,hu]
        rfl
      · simp only [List.length_cons]
        omega

theorem actual_prefix (n : Nat) :
    ∃ v,core n=List.replicate (n/2) A ++ v ∧ v.length=n+1-n/2 := by
  obtain ⟨v,hv,len⟩ := erase_prefix (n/2) (List.replicate (n+1) C) (by simp;omega)
  refine ⟨rounds (n%2) v,?_,?_⟩
  · unfold core
    have split := rounds_add (2*(n/2)) (n%2) (List.replicate (n+1) C)
    rw [show 2*(n/2)+n%2=n by omega] at split
    rw [split,hv,rounds_A_prefix]
  · rw [rounds_length,len,List.length_replicate]

theorem act_A_zero_stream : act A zero=zero := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem word_append (w v : List St) (x : Stream) :
    wordAct (w++v) x=wordAct v (wordAct w x) := by
  induction w generalizing x with
  | nil => rfl
  | cons s w ih => exact ih (act s x)

theorem A_word_zero (k : Nat) : wordAct (List.replicate k A) zero=zero := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ,wordAct,act_A_zero_stream,ih]

/-- Exact attained minimum. Time/age is n+1, with the center at fixed position 0. -/
theorem exact_minimum_positive_length (n : Nat) :
    (∃ w : List St,w.length=(n+3)/2 ∧ wordAct w zero=wordAct (core n) zero) ∧
    (∀ w : List St,wordAct w zero=wordAct (core n) zero → (n+3)/2≤w.length) := by
  constructor
  · obtain ⟨v,hv,len⟩ := actual_prefix n
    refine ⟨v,by omega,?_⟩
    rw [hv,word_append,A_word_zero]
  · intro w rep
    have h := representative_length n w rep
    omega

#print axioms SectionCompression.exact_minimum_positive_length
end SectionCompression
