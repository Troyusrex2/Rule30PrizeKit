module
public import ReachabilityBarrier
@[expose] public section
open Ruliology.CellularAutomata.Rule30FrozenRuler
open ReturnActions ReturnSections ReachabilityBarrier
example : ∀ (n : Nat) (x : CanonicalDecoration.Code),
    (∀ j,j<n → iter 8 x j=x j) → returnWord n 8 x≠bad := bad_unreachable
example : ∀ i : Fin 6, run (bad++bad) (bits 42) i.val=bits 42 i.val := bad_square_fixed_left
example : ∀ i : Fin 6, run (bad++bad) (bits 43) i.val=bits 43 i.val := bad_square_fixed_right
example : sectionWord (bad++bad) (bits 42) 6=sectionWord (bad++bad) (bits 43) 6 := bad_square_merges
example : bits 42 0≠bits 43 0 := bad_prefixes_distinct
