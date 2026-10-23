module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks12Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf11 : colConst K (Z &&& Q 11) (b 11) = true := by decide +kernel
theorem qf12 : colConst K (Z &&& Q 12) (b 12) = true := by decide +kernel
theorem qf13 : colConst K (Z &&& Q 13) (b 13) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
