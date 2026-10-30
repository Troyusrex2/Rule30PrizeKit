import Mathlib.Algebra.Group.Defs
import Ruliology.CellularAutomata.Rule30GroupCocycle

/-! Optional Mathlib adapter, outside the dependency-free catalog.
The explicit core GroupData are exactly the conventional group laws. -/
namespace StandardGroupAdapter
open Ruliology.CellularAutomata.Rule30GroupCocycle
universe u

@[instance_reducible] def fromMathlib (G : Type u) [Group G] : GroupData G where
  mul := fun a b => a*b
  ofNat := (1 : G)
  inv := fun a => a⁻¹
  assoc := _root_.mul_assoc
  left_unit := _root_.one_mul
  right_unit := _root_.mul_one
  left_inverse := _root_.inv_mul_cancel
  right_inverse := _root_.mul_inv_cancel

theorem conventional_group_background (G : Type) [Group G] (n : Nat)
    (L : Word (n+1) → G) (M : Word (n+2) → G)
    (h : letI : GroupData G := fromMathlib G; Cocycle L M) :
    ∃ g : Word n → G, g (zeros n)=1 ∧
      L (zeros (n+1))*M (zeros (n+2))=M (zeros (n+2))*L (zeros (n+1)) ∧
      (∀ w : Word (n+1), L w=(g (WordOps.tail w))⁻¹*L (zeros (n+1))*g (WordOps.init w)) ∧
      (∀ w : Word (n+2), M w=(g (image w))⁻¹*M (zeros (n+2))*g (middle w)) := by
  let : GroupData G := fromMathlib G
  exact full_background_connection G n L M h

end StandardGroupAdapter
