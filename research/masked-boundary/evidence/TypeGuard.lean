import MaskedTransport
open Ruliology.CellularAutomata Rule30DrivenLeft
example (c : Nat → Bool) (s : Int → Bool) :
    (∀ t p, p<0 → L c s t p=L (MaskedTransport.effective c) s t p) ↔
      MaskedTransport.FallingPins c s := MaskedTransport.transport_iff_falling c s
example : MaskedTransport.PeriodicMaskExclusion → Rule30Prize.Problem1 :=
  MaskedTransport.problem1_of_periodic_mask_exclusion
