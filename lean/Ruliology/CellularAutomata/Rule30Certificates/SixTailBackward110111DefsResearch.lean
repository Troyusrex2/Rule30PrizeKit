module

public import Ruliology.CellularAutomata.Rule30BackwardVacuumResearch

@[expose] public section

/-! Generated exact predecessor sets for `0^0 110111` at width 8.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110111
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 8
def N : Nat := 0
def tail : List Bool := [true,true,false,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 14134776518227275503921912379727790871922952195198546151671126788784783360
  | 3 => 220855883097298041197912187592864814479084524216769223218767087739600896
  | 4 => 68719476736
  | 5 => 57896044618658097711785492504343953926805133516280751251460479307672448925696
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110111
