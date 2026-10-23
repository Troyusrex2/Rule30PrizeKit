module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks13Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf14 : colConst K (Z &&& Q 14) (b 14) = true := by decide +kernel
theorem pf2 : colConst K (S 2 &&& P 2) (c 2) = true := by decide +kernel
theorem pf3 : colConst K (S 3 &&& P 3) (c 3) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
