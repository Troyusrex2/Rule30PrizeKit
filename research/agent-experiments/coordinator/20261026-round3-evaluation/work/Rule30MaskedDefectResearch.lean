module
public import Ruliology.CellularAutomata.Rule30Prize

/-! Conditional identities for a periodically matching center. The first gate
was proposed by Photograde's round-three response. The second-column identity
and necessary right admissibility explain why naive density contraction fails.
These are necessary conditions, not a proof of Prize Problem 1. -/
@[expose] public section
namespace Rule30MaskedDefectResearch
open Ruliology.CellularAutomata
open Rule30Jen

def defect (P t : Nat) (p : Int) : Bool := xor (cell t p) (cell (t+P) p)

theorem gate_local : ∀ al ac ar bl bc br : Bool,
    ac=bc → rule al ac ar=rule bl bc br →
    xor al bl=(!ac && xor ar br) := by decide +kernel

theorem white_gate (P t : Nat)
    (h0 : cell (t+P) 0=cell t 0)
    (h1 : cell (t+P+1) 0=cell (t+1) 0) :
    defect P t (-1)=(!cell t 0 && defect P t 1) := by
  exact gate_local (cell t (-1)) (cell t 0) (cell t 1)
    (cell (t+P) (-1)) (cell (t+P) 0) (cell (t+P) 1) h0.symm h1.symm

theorem second_local : ∀ a2 a1 a0 b2 b1 b0 : Bool,
    a0=b0 → (xor a1 b1 && a0)=false →
    xor a2 b2=xor (xor (rule a2 a1 a0) (rule b2 b1 b0)) (xor a1 b1) := by
  decide +kernel

theorem second_left_difference (P t : Nat)
    (h0 : cell (t+P) 0=cell t 0)
    (h1 : cell (t+P+1) 0=cell (t+1) 0) :
    defect P t (-2)=xor (defect P (t+1) (-1)) (defect P t (-1)) := by
  have gate := white_gate P t h0 h1
  have hz : (defect P t (-1) && cell t 0)=false := by
    rw [gate]
    cases cell t 0 <;> simp
  unfold defect
  rw [show t+1+P=t+P+1 by omega]
  exact second_local (cell t (-2)) (cell t (-1)) (cell t 0)
    (cell (t+P) (-2)) (cell (t+P) (-1)) (cell (t+P) 0) h0.symm hz

/-- A black right-adjacent cell has its next value fixed, even before the
next right column is known. A free boundary sequence need not satisfy this. -/
theorem right_admissibility (t : Nat) (h : cell t 1=true) :
    cell (t+1) 1=(!cell t 0) := by
  change rule (cell t 0) (cell t 1) (cell t 2)=_
  rw [h]
  cases cell t 0 <;> rfl

/-- If the center were eventually P-periodic, white center phases would
expose defects in column +1 arbitrarily late. This does not exclude them. -/
theorem periodic_center_white_defects (T P : Nat) (hP : 0<P)
    (hper : ∀ t, T ≤ t → cell (t+P) 0=cell t 0) (N : Nat) :
    ∃ t, N ≤ t ∧ cell t 0=false ∧ defect P t 1=true := by
  apply Classical.byContradiction
  intro hn
  have hleft : ∀ t, max T N ≤ t → cell (t+P) (-1)=cell t (-1) := by
    intro t ht
    have h0 := hper t (by omega)
    have h1 : cell (t+P+1) 0=cell (t+1) 0 := by
      rw [show t+P+1=(t+1)+P by omega]
      exact hper (t+1) (by omega)
    have hz : (!cell t 0 && defect P t 1)=false := by
      cases hc : cell t 0 with
      | true => rfl
      | false =>
        cases hd : defect P t 1 with
        | false => rfl
        | true => exact False.elim (hn ⟨t,by omega,hc,hd⟩)
    have he : defect P t (-1)=false := (white_gate P t h0 h1).trans hz
    cases ha : cell t (-1) <;> cases hb : cell (t+P) (-1) <;> simp_all [defect]
  exact not_adjacent (-1) ⟨max T N,P,hP,hleft⟩ ⟨T,P,hP,hper⟩

end Rule30MaskedDefectResearch
