module

public import Ruliology.CellularAutomata.Rule30BackwardVacuumResearch

@[expose] public section

/-! Generated exact predecessor sets for `0^0 101011` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101011
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,false,true,false,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 16
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101011
