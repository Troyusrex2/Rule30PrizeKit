module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks5Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q4 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 5) (Q 4) = true := by decide +kernel
theorem q5 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 6) (Q 5) = true := by decide +kernel
theorem q6 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 7) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
