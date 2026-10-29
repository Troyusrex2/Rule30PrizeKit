import Ruliology.CellularAutomata.Rule30DrivenMaskTransport
open Ruliology.CellularAutomata Rule30DrivenLeft
example (c : Nat → Bool) (s : Int → Bool) :
    (∀ t p, p<0 → L c s t p=L (Ruliology.CellularAutomata.Rule30DrivenMaskTransport.effective c) s t p) ↔
      Ruliology.CellularAutomata.Rule30DrivenMaskTransport.FallingPins c s := Ruliology.CellularAutomata.Rule30DrivenMaskTransport.transport_iff_falling c s
example : Ruliology.CellularAutomata.Rule30DrivenMaskTransport.PeriodicMaskExclusion → Rule30Prize.Problem1 :=
  Ruliology.CellularAutomata.Rule30DrivenMaskTransport.problem1_of_periodic_mask_exclusion
