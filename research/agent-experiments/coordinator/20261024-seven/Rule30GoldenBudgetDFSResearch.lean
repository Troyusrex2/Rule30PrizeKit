import Rule30GoldenBudgetResearch

/-! A depth-first version avoids materializing an entire prefix frontier.
The soundness theorem follows an arbitrary golden stream through the tree;
resource bounds and successful closed calculations remain separate. -/

namespace Rule30GoldenBudgetDFSResearch
open Rule30GoldenDFAResearch (Golden)
open Rule30GoldenEvenSupportResearch (Matches code)
open Rule30GoldenBudgetResearch (Node child count)

def prune (b : Nat) (q : Node) : Bool :=
  Rule30GoldenDFAResearch.empty q.st.flags || decide (b < q.used)

noncomputable def dfs (b : Nat) : Nat → Nat → Node → Bool
  | 0, _, q => prune b q
  | fuel+1,d,q => if prune b q then true else
      dfs b fuel (d+1) (child d q false) && dfs b fuel (d+1) (child d q true)

noncomputable def check (b K : Nat) : Bool :=
  dfs b K 0 ⟨Rule30GoldenEvenSupportResearch.start 1,0⟩

noncomputable def path (u : Nat) : Nat → Node
  | 0 => ⟨Rule30GoldenEvenSupportResearch.start 1,0⟩
  | d+1 => child d (path u d) (u.testBit d)

theorem dfs_of_prune {b fuel d : Nat} {q : Node} (h : prune b q = true) :
    dfs b fuel d q = true := by
  cases fuel with
  | zero => exact h
  | succ fuel => rw [dfs,h];rfl

theorem dfs_of_children {b fuel d : Nat} {q : Node}
    (h0 : dfs b fuel (d+1) (child d q false) = true)
    (h1 : dfs b fuel (d+1) (child d q true) = true) : dfs b (fuel+1) d q = true := by
  rw [dfs]
  cases h : prune b q
  · simp only [h,Bool.false_eq_true,↓reduceIte,h0,h1,Bool.and_self]
  · rfl

theorem count_mono (s : Nat → Bool) {m n : Nat} (hmn : m ≤ n) : count s m ≤ count s n := by
  induction n generalizing m with
  | zero =>
    have hm : m=0 := by omega
    subst m
    exact Nat.le_refl _
  | succ n ih =>
    by_cases hm : m ≤ n
    · have ht : count s n ≤ count s (n+1) := by rw [count];omega
      exact Nat.le_trans (ih hm) ht
    · have he : m=n+1 := by omega
      subst m
      exact Nat.le_refl _

theorem prune_false {b d : Nat} {s : Nat → Bool} {q : Node} (hg : Golden s)
    (hm : Matches s 0 d q.st) (hu : q.used = count s d) (hb : count s d ≤ b) :
    prune b q = false := by
  have hn := Rule30GoldenDFAResearch.not_empty_of_contains (Rule30GoldenDFAResearch.run_lt hg d) hm.2.2
  have he : Rule30GoldenDFAResearch.empty q.st.flags = false := by
    cases h : Rule30GoldenDFAResearch.empty q.st.flags
    · rfl
    · exact False.elim (hn h)
  have ht : ¬ b < q.used := by rw [hu];omega
  simp only [prune,he,decide_eq_false ht,Bool.or_self]

theorem dfs_sound {b : Nat} {s : Nat → Bool} (hg : Golden s) :
    ∀ fuel d q, Matches s 0 d q.st → q.used = count s d → count s (d+fuel) ≤ b →
      dfs b fuel d q ≠ true := by
  intro fuel
  induction fuel with
  | zero =>
    intro d q hm hu hb hc
    have hp := prune_false hg hm hu (by simpa only [Nat.add_zero] using hb)
    rw [dfs,hp] at hc
    cases hc
  | succ fuel ih =>
    intro d q hm hu hb hc
    have hd : count s d ≤ b := Nat.le_trans (count_mono s (by omega)) hb
    have hp := prune_false hg hm hu hd
    rw [dfs,hp] at hc
    have hboth : dfs b fuel (d+1) (child d q false) = true ∧
        dfs b fuel (d+1) (child d q true) = true := by
      simpa using hc
    have hn : count s (d+1) ≤ b := Nat.le_trans (count_mono s (by omega)) hb
    have hchild := Rule30GoldenBudgetResearch.child_matches hg hm hu hn
    have hactual : dfs b fuel (d+1) (child d q (code s d)) = true := by
      cases he : code s d
      · simpa only [he] using hboth.1
      · simpa only [he] using hboth.2
    apply ih (d+1) (child d q (code s d)) hchild.1 hchild.2.1 _ hactual
    simpa only [show d+1+fuel = d+(fuel+1) by omega] using hb

theorem no_golden_of_check {b K : Nat} (hc : check b K = true) (s : Nat → Bool)
    (hb : count s K ≤ b) : ¬ Golden s := by
  intro hg
  exact dfs_sound hg K 0 ⟨Rule30GoldenEvenSupportResearch.start 1,0⟩
    (Rule30GoldenEvenSupportResearch.start_matches rfl s) rfl (by simpa using hb) hc

end Rule30GoldenBudgetDFSResearch
