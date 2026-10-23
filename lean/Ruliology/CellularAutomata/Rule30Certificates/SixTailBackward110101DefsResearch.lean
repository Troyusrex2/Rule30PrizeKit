module

public import Ruliology.CellularAutomata.Rule30BackwardVacuumResearch

@[expose] public section

/-! Generated exact predecessor sets for `0^2 110101` at width 7.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 7
def N : Nat := 2
def tail : List Bool := [true,true,false,true,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 65536
  | 2 => 1329227995784920595342347523963486208
  | 3 => 42701449364590422419349652019974512680
  | 4 => 75557863725914324467728
  | 5 => 332306998946228968243966163579584512
  | 6 => 9444732965739290689536
  | 7 => 170141183460469231740910675752738881536
  | 8 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101
