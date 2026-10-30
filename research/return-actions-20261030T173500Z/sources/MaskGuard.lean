module
public import MaskDynamics
@[expose] public section
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration MaskDynamics
example : ∀ (x y : Code) (j : Nat),
    x (j+1)≠y (j+1) → x (j+2)=y (j+2) → x (j+3)=y (j+3) →
    T x (j+2)=T y (j+2) → T x (j+3)=T y (j+3) →
    T x (j+2)=false ∧ T y (j+2)=false := stall_turns_white
example : ∀ (x y : Code) (j : Nat),
    x (j+1)≠y (j+1) → x (j+2)=y (j+2) → x (j+3)=y (j+3) →
    T x (j+2)=T y (j+2) → T x (j+3)=T y (j+3) → T x (j+1)≠T y (j+1) →
    T (T x) (j+3)≠T (T y) (j+3) := two_step_escape
-- The control is a DIFFERENT gate, named in the statement.
example (x : Code) (j : Nat) :
    T210 x (j+2)=xor (x (j+2)) (!(x (j+1)) && x j) := rfl
example : ∀ t j,3≤j → iter210 t wallX j=iter210 t wallY j :=
  different_gate_has_trapped_pair.2.2.2.2
