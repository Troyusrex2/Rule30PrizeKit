module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks6Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem pf4 : colConst K (S 4 &&& P 4) (c 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
