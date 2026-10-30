module
import TwoLayerEscape
import ControlledAlias
open Ruliology.CellularAutomata.Rule30FrozenRuler
example (j : Nat) (x y : Nat → Bool) (hx : x 0=true)
    (low : ∀ k,k<j+1 → x k=y k) (ne : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+2 ∧
      (iter t x (j+3)≠iter t y (j+3) ∨ iter t x (j+4)≠iter t y (j+4)) :=
  TwoLayerEscape.two_layer_escape j x y hx low ne
example (t : Nat) (x : Nat → Bool) : ControlledAlias.driven (t+1) x=
    ControlledAlias.U (ControlledAlias.lowerC (ControlledAlias.drive (ControlledAlias.phase t)))
      (ControlledAlias.lowerH (ControlledAlias.drive (ControlledAlias.phase t)))
      (ControlledAlias.driven t x) := ControlledAlias.act_is_controlled _ _
example : ∀ t j,5≤j →
    ControlledAlias.driven t (Nat.testBit 42) j=ControlledAlias.driven t (Nat.testBit 43) j :=
  ControlledAlias.controlled_confined
