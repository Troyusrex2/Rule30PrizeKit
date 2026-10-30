module
public import Ruliology.CellularAutomata.Rule30FrozenRuler

/-! An explicit canonical confined partner for every realignment.
Existence is unconditional; uniqueness is equivalent to the still-open
same-edge rigidity property. No orbit census or hazard estimate is used. -/
@[expose] public section
namespace CanonicalDecoration
open Ruliology.CellularAutomata.Rule30FrozenRuler

abbrev Code := Nat → Bool

def H (x : Code) : Code
  | 0 => true
  | 1 => !(x 1)
  | j+2 => x (j+1)

theorem H_edge (x : Code) : H x 0=true := rfl

theorem H_shift (x : Code) (j : Nat) (hj : 1≤j) : H x (j+1)=x j := by
  cases j with
  | zero => omega
  | succ j => rfl

def parent (y : Code) : Code
  | 0 => true
  | j+1 => y (j+2)

theorem H_parent_iff (y : Code) (hy : y 0=true) :
    H (parent y)=y ↔ y 1= !(y 2) := by
  constructor
  · intro h
    have h1 := congrFun h 1
    exact h1.symm
  · intro h
    funext j
    cases j with
    | zero => exact hy.symm
    | succ j =>
      cases j with
      | zero => exact h.symm
      | succ j => rfl

theorem H_injective (x y : Code) (hx : x 0=true) (hy : y 0=true)
    (h : H x=H y) : x=y := by
  funext j
  cases j with
  | zero => exact hx.trans hy.symm
  | succ j => exact congrFun h (j+2)

/-- Complementary inserted digits keep the OR drive constant. -/
theorem H_commutes (x : Code) (h0 : x 0=true) : T (H x)=H (T x) := by
  funext j
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => simp only [T,H,h0];cases x 1 <;> rfl
    | succ j =>
      cases j with
      | zero => simp only [T,H,h0];cases x 1 <;> rfl
      | succ j =>
        cases j with
        | zero => simp only [T,H,h0];cases x 1 <;> cases x 2 <;> rfl
        | succ j => rfl

def decorate : Nat → Code → Code
  | 0,x => x
  | D+1,x => H (decorate D x)

theorem decorate_edge (D : Nat) (x : Code) (h0 : x 0=true) :
    decorate D x 0=true := by
  cases D with
  | zero => exact h0
  | succ D => rfl

theorem decorate_shift (D : Nat) (x : Code) (j : Nat) (hj : 1≤j) :
    decorate D x (j+D)=x j := by
  induction D with
  | zero => rfl
  | succ D ih =>
    change H (decorate D x) (j+(D+1))=x j
    rw [show j+(D+1)=(j+D)+1 by omega,H_shift _ _ (by omega),ih]

theorem decorate_commutes (D : Nat) (x : Code) (h0 : x 0=true) :
    T (decorate D x)=decorate D (T x) := by
  induction D with
  | zero => rfl
  | succ D ih =>
    change T (H (decorate D x))=H (decorate D (T x))
    rw [H_commutes _ (decorate_edge D x h0),ih]

theorem iter_decorate (D : Nat) (x : Code) (h0 : x 0=true) :
    ∀ t,iter t (decorate D x)=decorate D (iter t x) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    change T (iter t (decorate D x))=decorate D (T (iter t x))
    rw [ih,decorate_commutes D _]
    simpa only [iter_zero] using h0

def Confined (K D : Nat) (x y : Code) : Prop :=
  ∀ t j,K+1≤j → iter t y (j+D)=iter t x j

/-- Every band and realignment, every infinite code with a black edge. -/
theorem canonical_confined (K D : Nat) (x : Code) (h0 : x 0=true) :
    Confined K D x (decorate D x) := by
  intro t j hj
  rw [iter_decorate D x h0 t,decorate_shift D _ j (by omega)]

def SameEdgeRigidity : Prop := ∀ (K : Nat) (x y : Code),
  x 0=true → y 0=true → Confined K 0 x y → x=y

def CanonicalClassification : Prop := ∀ (K D : Nat) (x y : Code),
  x 0=true → y 0=true → Confined K D x y → y=decorate D x

/-- All realignments reduce to same-edge rigidity, without an induction
classifying arbitrary D-step decoration chains. Rigidity is a hypothesis. -/
theorem classification_of_same_edge (rigidity : SameEdgeRigidity) :
    CanonicalClassification := by
  intro K D x y hx hy confined
  have same : Confined (K+D) 0 (decorate D x) y := by
    intro t i hi
    have hj : K+1≤i-D := by omega
    have hc := confined t (i-D) hj
    have hz := canonical_confined K D x hx t (i-D) hj
    have index : i-D+D=i := by omega
    simpa only [Nat.add_zero,index] using hc.trans hz.symm
  exact (rigidity (K+D) (decorate D x) y (decorate_edge D x hx) hy same).symm

theorem same_edge_of_classification (classification : CanonicalClassification) :
    SameEdgeRigidity := by
  intro K x y hx hy confined
  exact (classification K 0 x y hx hy confined).symm

theorem classification_iff_same_edge : CanonicalClassification ↔ SameEdgeRigidity :=
  ⟨same_edge_of_classification,classification_of_same_edge⟩

end CanonicalDecoration
