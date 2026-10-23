module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks10Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf5 : colConst K (Z &&& Q 5) (b 5) = true := by decide +kernel
theorem qf6 : colConst K (Z &&& Q 6) (b 6) = true := by decide +kernel
theorem qf7 : colConst K (Z &&& Q 7) (b 7) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
