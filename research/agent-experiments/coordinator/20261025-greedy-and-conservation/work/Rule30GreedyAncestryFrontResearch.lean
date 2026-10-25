module
public import Rule30RoundTwoAncestryFrontResearch

/-! A least-source descendant set is a left cut of all disagreements. With
its rightmost descendant at r, the next descendant set is exactly the next
disagreements at positions <=r+1. This is a greedy rule, not a progress bound. -/
@[expose] public section
namespace Rule30GreedyAncestryFrontResearch
open CedarAncestry Rule30RoundTwoAncestryFrontResearch

def Cut (d : Nat → Int → Bool) (source : Int) (t : Nat) (r : Int) : Prop :=
  ∀ x, Root d source t x ↔ d t x=true ∧ x≤r

theorem root_cut_of_rightmost (d : Nat → Int → Bool) (source : Int)
    (hstep : ∀ t x, d (t+1) x=true → d t (parent (d t) x)=true)
    (hmin : ∀ x, d 0 x=true → source≤x) (t : Nat) (r : Int)
    (hr : Root d source t r)
    (hmax : ∀ x, Root d source t x → x≤r) : Cut d source t r := by
  intro x
  constructor
  · intro hx; exact ⟨hx.1,hmax x hx⟩
  · rintro ⟨hd,hxr⟩
    refine ⟨hd,?_⟩
    have hu := ancestor_monotone d t x r hxr
    rw [hr.2] at hu
    have hl := hmin _ (ancestor_valid d hstep t x hd)
    exact Int.le_antisymm hu hl

/-- Every next disagreement at or to the left of r+1 has the least source;
all next disagreements strictly to its right have another source. -/
theorem cut_successor (d : Nat → Int → Bool) (source : Int)
    (hstep : ∀ t x, d (t+1) x=true → d t (parent (d t) x)=true)
    (hmin : ∀ x, d 0 x=true → source≤x) (t : Nat) (r : Int)
    (hcut : Cut d source t r) (hr : d t r=true) (x : Int) :
    Root d source (t+1) x ↔ d (t+1) x=true ∧ x≤r+1 := by
  rw [least_root_recurrence d source hstep hmin]
  constructor
  · rintro ⟨hd,y,hlo,hhi,hy⟩
    have hyr := ((hcut y).mp hy).2
    exact ⟨hd,by omega⟩
  · rintro ⟨hd,hx⟩
    have hp := hstep t x hd
    have hpr : parent (d t) x≤r := by
      by_cases hn : r≤x+1
      · exact parent_le_neighbor (d t) x r (by omega) hn hr
      · have hb := (parent_bounds (d t) x).2
        omega
    exact ⟨hd,parent (d t) x,(parent_bounds (d t) x).1,
      (parent_bounds (d t) x).2,(hcut _).mpr ⟨hp,hpr⟩⟩

/-- Exact successor criterion for a candidate rightmost descendant. It may
retreat arbitrarily far; no lower bound on r' is hidden in this statement. -/
theorem greedy_frontier (d : Nat → Int → Bool) (source : Int)
    (hstep : ∀ t x, d (t+1) x=true → d t (parent (d t) x)=true)
    (hmin : ∀ x, d 0 x=true → source≤x) (t : Nat) (r r' : Int)
    (hcut : Cut d source t r) (hr : d t r=true)
    (hr' : d (t+1) r'=true) (hbelow : r'≤r+1)
    (hgap : ∀ x, r'<x → x≤r+1 → d (t+1) x=false) :
    Root d source (t+1) r' ∧ Cut d source (t+1) r' := by
  have hc := cut_successor d source hstep hmin t r hcut hr
  refine ⟨(hc r').mpr ⟨hr',hbelow⟩,?_⟩
  intro x
  rw [hc x]
  constructor
  · rintro ⟨hd,hx⟩
    have hn : ¬r'<x := by
      intro hgt
      rw [hgap x hgt hx] at hd
      cases hd
    exact ⟨hd,by omega⟩
  · rintro ⟨hd,hx⟩
    exact ⟨hd,by omega⟩

end Rule30GreedyAncestryFrontResearch
