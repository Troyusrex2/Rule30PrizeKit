module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks9Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf2 : colConst K (Z &&& Q 2) (b 2) = true := by decide +kernel
theorem qf3 : colConst K (Z &&& Q 3) (b 3) = true := by decide +kernel
theorem qf4 : colConst K (Z &&& Q 4) (b 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
