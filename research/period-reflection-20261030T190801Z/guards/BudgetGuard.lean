module
import Ruliology.CellularAutomata.Rule30DefectClockBudget
open Ruliology.CellularAutomata.Rule30FrozenRuler
open Ruliology.CellularAutomata.Rule30DefectClockBudget
example (j s : Nat) (x y : Nat → Bool) (hx : x 0=true)
    (low : ∀ k,k<j+1 → x k=y k) (ne : x (j+1)≠y (j+1)) :
    ∃ t,t≤7*((j+1)/2+1) ∧
      (iter (s+t) x (j+5)≠iter (s+t) y (j+5) ∨
       iter (s+t) x (j+6)≠iter (s+t) y (j+6)) :=
  recurrent_four_layer_escape j s x y hx low ne
example (j : Nat) (x y : Nat → Bool) : measure j x y≤6 := measure_bound j x y
