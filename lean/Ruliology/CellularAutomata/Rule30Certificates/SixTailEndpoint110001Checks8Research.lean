module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks7Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q10 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 11) (Q 10) = true := by decide +kernel
theorem q11 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 12) (Q 11) = true := by decide +kernel
theorem q12 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 13) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
