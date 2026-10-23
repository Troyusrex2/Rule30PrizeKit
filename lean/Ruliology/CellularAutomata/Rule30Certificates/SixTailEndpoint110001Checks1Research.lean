module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks0Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem p1 : preCheck K (tail.getD 1 false) (P 1) (P 2) = true := by decide +kernel
theorem p2 : preCheck K (tail.getD 2 false) (P 2) (P 3) = true := by decide +kernel
theorem p3 : preCheck K (tail.getD 3 false) (P 3) (P 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
