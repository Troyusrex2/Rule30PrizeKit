module
public import CedarAncestry

/-! Formal follow-up to Cedar's R2-04 response. These are bridges and
recurrences, not a proof of the unproved least-root escape premise. -/
@[expose] public section
namespace Rule30RoundTwoAncestryFrontResearch
open Ruliology.CellularAutomata
open CedarAncestry

def Root (d : Nat → Int → Bool) (r : Int) (t : Nat) (x : Int) : Prop :=
  d t x = true ∧ ancestor d t x = r

theorem parent_le_neighbor (d : Int → Bool) (x y : Int)
    (hlo : x-1 ≤ y) (hhi : y ≤ x+1) (hy : d y = true) :
    parent d x ≤ y := by
  have cases_y : y=x-1 ∨ y=x ∨ y=x+1 := by omega
  rcases cases_y with h | h | h
  · subst y; simp [parent, hy]
  · subst y
    by_cases hl : d (x-1)=true <;> simp [parent,hl,hy] <;> omega
  · subst y; exact (parent_bounds d x).2

/-- The whole descendant set of the least root has the exact masked-neighbor
recurrence. This justifies the packed frontier experiment without assuming a
center survivor or monotone frontier movement. -/
theorem least_root_recurrence (d : Nat → Int → Bool) (r : Int)
    (hstep : ∀ t x, d (t+1) x = true → d t (parent (d t) x) = true)
    (hmin : ∀ x, d 0 x = true → r ≤ x) (t : Nat) (x : Int) :
    Root d r (t+1) x ↔ d (t+1) x = true ∧
      ∃ y, x-1 ≤ y ∧ y ≤ x+1 ∧ Root d r t y := by
  constructor
  · rintro ⟨hd,hr⟩
    exact ⟨hd, parent (d t) x, (parent_bounds (d t) x).1,
      (parent_bounds (d t) x).2, hstep t x hd, hr⟩
  · rintro ⟨hd,y,hlo,hhi,hy,hr⟩
    refine ⟨hd,?_⟩
    have hp := hstep t x hd
    have upper := ancestor_monotone d t _ _ (parent_le_neighbor (d t) x y hlo hhi hy)
    rw [hr] at upper
    have lower := hmin _ (ancestor_valid d hstep t _ hp)
    exact Int.le_antisymm upper lower

theorem canonical_parent_valid (T P t : Nat) (x : Int)
    (h : canonicalDiff T P (t+1) x = true) :
    canonicalDiff T P t (parent (canonicalDiff T P t) x) = true := by
  apply parent_valid30 (Rule30Jen.cell (T+t)) (Rule30Jen.cell (T+P+t)) x
  simpa [canonicalDiff, diff, out, Rule30Jen.cell, Rule30Jen.rule,
    Nat.add_assoc] using h

theorem canonical_below_left_edge (T P t : Nat) (x : Int)
    (hx : x < -((T+P+t : Nat) : Int)) : canonicalDiff T P t x = false := by
  unfold canonicalDiff diff
  rw [Rule30Jen.cell_eq_false_of_lt (T+t) x (by omega),
    Rule30Jen.cell_eq_false_of_lt (T+P+t) x hx]
  rfl

theorem canonical_initial_minimum (T P : Nat) (x : Int)
    (h : canonicalDiff T P 0 x = true) : -((T+P : Nat) : Int) ≤ x := by
  by_cases good : -((T+P : Nat) : Int) ≤ x
  · exact good
  have hx : x < -((T+P+0 : Nat) : Int) := by omega
  rw [canonical_below_left_edge T P 0 x hx] at h
  cases h

theorem canonical_root_recurrence (T P t : Nat) (x : Int) :
    Root (canonicalDiff T P) (-((T+P : Nat) : Int)) (t+1) x ↔
      canonicalDiff T P (t+1) x = true ∧
      ∃ y, x-1 ≤ y ∧ y ≤ x+1 ∧
        Root (canonicalDiff T P) (-((T+P : Nat) : Int)) t y := by
  exact least_root_recurrence _ _ (canonical_parent_valid T P)
    (canonical_initial_minimum T P) t x

/-- The expanding left boundary is always a disagreement for a positive lag. -/
theorem canonical_left_edge_disagrees (T P t : Nat) (hP : 0<P) :
    canonicalDiff T P t (-((T+P+t : Nat) : Int)) = true := by
  unfold canonicalDiff diff
  rw [Rule30Jen.cell_eq_false_of_lt (T+t) _ (by omega),
    Rule30Jen.cell_left_edge (T+P+t)]
  rfl

/-- The least initial source never disappears: the outward moving left edge
retains it forever. This is weaker than reaching the center. -/
theorem canonical_left_edge_keeps_root (T P : Nat) (hP : 0<P) (t : Nat) :
    Root (canonicalDiff T P) (-((T+P : Nat) : Int)) t
      (-((T+P+t : Nat) : Int)) := by
  refine ⟨canonical_left_edge_disagrees T P t hP,?_⟩
  induction t with
  | zero => rfl
  | succ t ih =>
    change ancestor (canonicalDiff T P) t
      (parent (canonicalDiff T P t) (-((T+P+(t+1) : Nat) : Int))) = _
    have h0 := canonical_below_left_edge T P t
      (-((T+P+(t+1) : Nat) : Int)) (by omega)
    have h1 := canonical_below_left_edge T P t
      (-((T+P+(t+1) : Nat) : Int)-1) (by omega)
    simp only [parent,h0,h1,Bool.false_eq_true,↓reduceIte]
    have eq : -((T+P+(t+1) : Nat) : Int)+1 = -((T+P+t : Nat) : Int) := by omega
    rw [eq]
    exact ih

/-- A nearest-neighbor descendant cannot cross zero without visiting it.
No lower bound on a retreat and no positive velocity are assumed. -/
theorem root_hits_zero_of_nonnegative (d : Nat → Int → Bool) (r : Int)
    (hr : r<0)
    (hstep : ∀ t x, d (t+1) x = true → d t (parent (d t) x) = true)
    (hescape : ∃ t x, 0≤x ∧ Root d r t x) : ∃ t, Root d r t 0 := by
  apply Classical.byContradiction
  intro hn
  have hzero : ∀ t, ¬ Root d r t 0 := by
    intro t ht
    exact hn ⟨t,ht⟩
  have hnegative : ∀ t x, Root d r t x → x<0 := by
    intro t
    induction t with
    | zero =>
      intro x hx
      change d 0 x=true ∧ x=r at hx
      omega
    | succ t ih =>
      intro x hx
      have hp : Root d r t (parent (d t) x) := ⟨hstep t x hx.1,hx.2⟩
      have hpneg := ih _ hp
      have bounds := parent_bounds (d t) x
      have hxzero : x≠0 := by
        intro eq
        subst x
        exact hzero (t+1) hx
      omega
  obtain ⟨t,x,hx,hroot⟩ := hescape
  have := hnegative t x hroot
  omega

def LeastRootEscape : Prop := ∀ T P : Nat, 0<P →
  ∃ t x, 0≤x ∧ Root (canonicalDiff T P) (-((T+P : Nat) : Int)) t x

/-- Conditional interface to the exact official full statement. The escape
premise is deliberately left unproved. -/
theorem problem1_of_least_root_escape (he : LeastRootEscape) :
    Rule30Prize.Problem1 := by
  rintro ⟨T,P,hP,hperiod⟩
  obtain ⟨t,ht⟩ := root_hits_zero_of_nonnegative (canonicalDiff T P)
    (-((T+P : Nat) : Int)) (by omega) (canonical_parent_valid T P) (he T P hP)
  have hp := hperiod (T+t) (by omega)
  have eq : T+P+t=T+t+P := by omega
  have hd := ht.1
  simp only [canonicalDiff,diff,Rule30Prize.center] at hd hp
  rw [eq,hp] at hd
  cases hc : Rule30Jen.cell (T+t) 0 <;> simp [hc] at hd

end Rule30RoundTwoAncestryFrontResearch
