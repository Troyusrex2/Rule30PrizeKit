import Rule30GoldenEvenSupportResearch

/-! A complete branching checker with a budget on black even coordinates.
No bound on the positions of those coordinates is assumed. Generic
soundness alone does not establish extinction for every budget. -/

namespace Rule30GoldenBudgetResearch
open Rule30GoldenDFAResearch (Golden)
open Rule30GoldenEvenSupportResearch (State Matches code)

structure Node where
  st : State
  used : Nat

noncomputable def child (d : Nat) (q : Node) (e : Bool) : Node :=
  ⟨Rule30GoldenEvenSupportResearch.step 1 (fun _ => e.toNat) d q.st, q.used+e.toNat⟩

noncomputable def next (b d : Nat) (xs : List Node) : List Node :=
  xs.flatMap fun q => ([child d q false,child d q true]).filter fun r =>
    decide (r.used ≤ b) && !Rule30GoldenDFAResearch.empty r.st.flags

noncomputable def frontier (b : Nat) : Nat → List Node
  | 0 => [⟨Rule30GoldenEvenSupportResearch.start 1,0⟩]
  | d+1 => next b d (frontier b d)

noncomputable def check (b K : Nat) : Bool := (frontier b K).isEmpty

def count (s : Nat → Bool) : Nat → Nat
  | 0 => 0
  | d+1 => count s d + (code s d).toNat

theorem count_le_index (s : Nat → Bool) (d : Nat) : count s d ≤ d := by
  induction d with
  | zero => exact Nat.le_refl 0
  | succ d ih =>
    rw [count]
    cases code s d <;> simp_all <;> omega

theorem child_matches {d b : Nat} {q : Node} {s : Nat → Bool} (hg : Golden s)
    (hm : Matches s 0 d q.st) (hu : q.used = count s d) (hb : count s (d+1) ≤ b) :
    Matches s 0 (d+1) (child d q (code s d)).st ∧
      (child d q (code s d)).used = count s (d+1) ∧
      (child d q (code s d)).used ≤ b ∧
      Rule30GoldenDFAResearch.empty (child d q (code s d)).st.flags = false := by
  have he : ((code s d).toNat).testBit 0 = code s d := by cases code s d <;> rfl
  have hstep := Rule30GoldenEvenSupportResearch.step_matches (ALL:=1) (p:=0)
    (E:=fun _ => (code s d).toNat) rfl hg he hm
  have hused : (child d q (code s d)).used = count s (d+1) := by simp only [child,count,hu]
  refine ⟨hstep,hused,by rw [hused];exact hb,?_⟩
  have hn := Rule30GoldenDFAResearch.not_empty_of_contains
    (Rule30GoldenDFAResearch.run_lt hg (d+1)) hstep.2.2
  cases h : Rule30GoldenDFAResearch.empty (child d q (code s d)).st.flags
  · rfl
  · exact False.elim (hn h)

theorem mem_next {b d : Nat} {xs : List Node} {q : Node} {s : Nat → Bool}
    (hq : q ∈ xs) (hg : Golden s) (hm : Matches s 0 d q.st)
    (hu : q.used = count s d) (hb : count s (d+1) ≤ b) :
    child d q (code s d) ∈ next b d xs := by
  have hc := child_matches hg hm hu hb
  apply List.mem_flatMap.mpr
  refine ⟨q,hq,?_⟩
  apply List.mem_filter.mpr
  constructor
  · cases code s d <;> simp
  · simp only [hc.2.2.1,decide_true,hc.2.2.2,Bool.not_false,Bool.and_self]

theorem frontier_contains {b : Nat} {s : Nat → Bool} (hg : Golden s) :
    ∀ d, count s d ≤ b → ∃ q ∈ frontier b d,
      Matches s 0 d q.st ∧ q.used = count s d := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨⟨Rule30GoldenEvenSupportResearch.start 1,0⟩,by simp [frontier],?_,rfl⟩
    exact Rule30GoldenEvenSupportResearch.start_matches rfl s
  | succ d ih =>
    intro hb
    have hp : count s d ≤ b := by rw [count] at hb; omega
    obtain ⟨q,hq,hm,hu⟩ := ih hp
    refine ⟨child d q (code s d),mem_next hq hg hm hu hb,?_,?_⟩
    · exact (child_matches hg hm hu hb).1
    · exact (child_matches hg hm hu hb).2.1

/-- A closed checker evaluation excludes a bounded number of black even
coordinates in the entire infinite row, with no spacing restriction. -/
theorem no_golden_of_check {b K : Nat} (hc : check b K = true) (s : Nat → Bool)
    (hb : count s K ≤ b) : ¬ Golden s := by
  intro hg
  obtain ⟨q,hq,_,_⟩ := frontier_contains hg K hb
  unfold check at hc
  cases h : frontier b K with
  | nil => simp only [h,List.not_mem_nil] at hq
  | cons a as => simp only [h,List.isEmpty_cons,Bool.false_eq_true] at hc

theorem count_le_support {M : Nat} {s : Nat → Bool}
    (hs : ∀ d, M ≤ d → code s d = false) : ∀ K, count s K ≤ M := by
  intro K
  induction K with
  | zero => simp only [count];omega
  | succ K ih =>
    by_cases hK : K < M
    · have ht := count_le_index s (K+1)
      omega
    · rw [count,hs K (by omega)]
      simpa using ih

theorem uniform_width_of_all_budget_checks
    (hc : ∀ b, ∃ K, check b K = true) (M : Nat) :
    Rule30GoldenEvenSupportResearch.NoGoldenEvenWidth M := by
  intro s hs
  obtain ⟨K,hK⟩ := hc M
  exact no_golden_of_check hK s (count_le_support hs K)

end Rule30GoldenBudgetResearch
