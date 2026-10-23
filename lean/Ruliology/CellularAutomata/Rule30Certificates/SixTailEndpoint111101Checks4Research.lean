module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks3Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem s4 : image K (tail.getD 4 false) (S 4) = S 5 := by decide +kernel
theorem s5 : image K (tail.getD 5 false) (S 5) = S 6 := by decide +kernel
theorem q0 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 1) (Q 0) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
