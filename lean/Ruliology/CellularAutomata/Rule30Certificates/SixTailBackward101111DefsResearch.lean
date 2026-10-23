module

public import Ruliology.CellularAutomata.Rule30BackwardVacuumResearch

@[expose] public section

/-! Generated exact predecessor sets for `0^6 101111` at width 6.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 6
def N : Nat := 6
def tail : List Bool := [true,false,true,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 256
  | 2 => 1152921504875282432
  | 3 => 288230376218820676
  | 4 => 549755815936
  | 5 => 144115205289279488
  | 6 => 36028797027385344
  | 7 => 281474976776192
  | 8 => 1099528405248
  | 9 => 35184908959752
  | 10 => 68719476736
  | 11 => 9223372039002259456
  | 12 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111
