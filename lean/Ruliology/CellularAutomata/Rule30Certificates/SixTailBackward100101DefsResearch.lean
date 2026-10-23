module

public import Ruliology.CellularAutomata.Rule30BackwardVacuumResearch

@[expose] public section

/-! Generated exact predecessor sets for `0^4 100101` at width 7.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 7
def N : Nat := 4
def tail : List Bool := [true,false,false,true,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 4722366482869645213696
  | 2 => 21267647932558653967613834469092360192
  | 3 => 5316911983139663565690434912111296576
  | 4 => 10141204801825835212523381458944
  | 5 => 309485009893402662762708992
  | 6 => 75557863725914324467728
  | 7 => 332306998946228968243966163579584512
  | 8 => 9444732965739290689536
  | 9 => 170141183460469231740910675752738881536
  | 10 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101
