module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks5Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf1 : colConst K (Z &&& Q 1) (b 1) = true := by decide +kernel
theorem qf2 : colConst K (Z &&& Q 2) (b 2) = true := by decide +kernel
theorem qf3 : colConst K (Z &&& Q 3) (b 3) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
