module
import ClockDelay
open Ruliology.CellularAutomata.Rule30FrozenRuler
example (n t j : Nat) (ht : t≤n+2) (hj : 2*n+5≤j) :
    iter t (ClockDelay.X n) j=iter t (ClockDelay.Y n) j :=
  ClockDelay.arbitrary_delay n t j ht hj
example (n : Nat) : ClockDelay.X n 0=true ∧ ClockDelay.Y n 0=true ∧
    ClockDelay.X n (2*n+3)≠ClockDelay.Y n (2*n+3) ∧
    (∀ j,2*n+6≤j → ClockDelay.X n j=false ∧ ClockDelay.Y n j=false) :=
  ⟨rfl,rfl,ClockDelay.first_difference n,ClockDelay.finite_pair n⟩
