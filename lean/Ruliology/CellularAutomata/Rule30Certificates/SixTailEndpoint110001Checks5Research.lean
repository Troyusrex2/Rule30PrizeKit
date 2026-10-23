module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks4Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q1 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 2) (Q 1) = true := by decide +kernel
theorem q2 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 3) (Q 2) = true := by decide +kernel
theorem q3 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 4) (Q 3) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
