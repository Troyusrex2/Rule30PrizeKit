module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks11Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf8 : colConst K (Z &&& Q 8) (b 8) = true := by decide +kernel
theorem qf9 : colConst K (Z &&& Q 9) (b 9) = true := by decide +kernel
theorem qf10 : colConst K (Z &&& Q 10) (b 10) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
