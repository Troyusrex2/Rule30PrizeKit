module
public import QuietClock
@[expose] public section
namespace TwoLayerEscape
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration QuietClock

theorem cancel_xor (u a b : Bool) (h : xor u a=xor u b) : a=b := by
  cases u <;> cases a <;> cases b <;> simp_all

theorem bool_two_stalls (a b p q u c a1 b1 : Bool)
    (ne : a≠b) (ne1 : a1≠b1)
    (h0 : (p||a)=(q||b)) (m0 : (u||p)=(u||q))
    (h1 : (xor p (a||c)||a1)=(xor q (b||c)||b1))
    (m1 : (xor u (p||a)||xor p (a||c))=
          (xor u (p||a)||xor q (b||c))) : c=false := by
  cases a <;> cases b <;> cases p <;> cases q <;> cases u <;>
    cases c <;> cases a1 <;> cases b1 <;> simp_all

/-- If both interface digits agree for three consecutive rows, the common
digit below the persistent lowest difference must currently be white. -/
theorem three_rows_force_white (x y : Code) (j : Nat)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1))
    (a0 : x (j+3)=y (j+3)) (b0 : x (j+4)=y (j+4))
    (a1 : T x (j+3)=T y (j+3)) (b1 : T x (j+4)=T y (j+4))
    (a2 : T (T x) (j+3)=T (T y) (j+3))
    (b2 : T (T x) (j+4)=T (T y) (j+4)) : x j=false := by
  have low:=below j (by omega)
  have next_ne : T x (j+1)≠T y (j+1) := iter_diff below different 1
  have h0 : (x (j+2)||x (j+1))=(y (j+2)||y (j+1)) := by
    apply cancel_xor (y (j+3))
    simpa only [T,a0] using a1
  have m0 : (x (j+3)||x (j+2))=(x (j+3)||y (j+2)) := by
    apply cancel_xor (y (j+4))
    simpa only [T,b0,←a0] using b1
  have h1 : (T x (j+2)||T x (j+1))=(T y (j+2)||T y (j+1)) := by
    apply cancel_xor (T y (j+3))
    change xor (T x (j+3)) (T x (j+2)||T x (j+1))=
      xor (T y (j+3)) (T y (j+2)||T y (j+1)) at a2
    rw [a1] at a2
    exact a2
  have m1 : (T x (j+3)||T x (j+2))=(T x (j+3)||T y (j+2)) := by
    apply cancel_xor (T y (j+4))
    change xor (T x (j+4)) (T x (j+3)||T x (j+2))=
      xor (T y (j+4)) (T y (j+3)||T y (j+2)) at b2
    rw [b1,←a1] at b2
    exact b2
  apply bool_two_stalls (x (j+1)) (y (j+1)) (x (j+2)) (y (j+2))
    (x (j+3)) (x j) (T x (j+1)) (T y (j+1)) different next_ne h0 m0
  · simpa only [T,low] using h1
  · simpa only [T,low] using m1

/-- Every persistent first difference escapes a band of two digits within
ceil(j/2)+2 ticks, including the exceptional first-difference digit 1. -/
theorem two_layer_escape (j : Nat) (x y : Code) (hx : x 0=true)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+2 ∧
      (iter t x (j+3)≠iter t y (j+3) ∨ iter t x (j+4)≠iter t y (j+4)) := by
  apply Classical.byContradiction
  intro none
  have same : ∀ t,t≤(j+1)/2+2 →
      iter t x (j+3)=iter t y (j+3) ∧ iter t x (j+4)=iter t y (j+4) := by
    intro t ht
    constructor
    · by_cases eq : iter t x (j+3)=iter t y (j+3)
      · exact eq
      · exact False.elim (none ⟨t,ht,Or.inl eq⟩)
    · by_cases eq : iter t x (j+4)=iter t y (j+4)
      · exact eq
      · exact False.elim (none ⟨t,ht,Or.inr eq⟩)
  have white : ∀ t,t≤(j+1)/2 → iter t x j=false := by
    intro t ht
    exact three_rows_force_white (iter t x) (iter t y) j
      (iter_agree below t) (iter_diff below different t)
      (same t (by omega)).1 (same t (by omega)).2
      (same (t+1) (by omega)).1 (same (t+1) (by omega)).2
      (same (t+2) (by omega)).1 (same (t+2) (by omega)).2
  by_cases zero : j=0
  · subst j
    have wrong:=white 0 (by omega)
    change x 0=false at wrong
    rw [hx] at wrong;cases wrong
  · obtain ⟨t,ht,ne⟩:=flip_bound j (by omega) x hx
    exact ne ((white t ht).trans (white 0 (by omega)).symm)

end TwoLayerEscape
