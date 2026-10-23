module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks6Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q7 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 8) (Q 7) = true := by decide +kernel
theorem q8 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 9) (Q 8) = true := by decide +kernel
theorem q9 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 10) (Q 9) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
