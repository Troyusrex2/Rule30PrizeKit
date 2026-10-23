module

public import Ruliology.CellularAutomata.Rule30BackwardVacuumResearch

@[expose] public section

/-! Generated exact predecessor sets for `0^2 111111` at width 6.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111111
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 6
def N : Nat := 2
def tail : List Bool := [true,true,true,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 256
  | 2 => 1152921504875282432
  | 3 => 576469548530665600
  | 4 => 1099528405248
  | 5 => 35184908959752
  | 6 => 68719476736
  | 7 => 9223372039002259456
  | 8 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111111
