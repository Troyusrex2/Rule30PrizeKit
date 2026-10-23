module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks8Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q13 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 14) (Q 13) = true := by decide +kernel
theorem qf0 : colConst K (Z &&& Q 0) (b 0) = true := by decide +kernel
theorem qf1 : colConst K (Z &&& Q 1) (b 1) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
