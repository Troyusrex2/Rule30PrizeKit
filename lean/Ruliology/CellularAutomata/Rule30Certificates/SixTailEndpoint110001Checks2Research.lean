module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks1Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem p4 : preCheck K (tail.getD 4 false) (P 4) (P 5) = true := by decide +kernel
theorem p5 : preCheck K (tail.getD 5 false) (P 5) (P 6) = true := by decide +kernel
theorem s0 : image K (tail.getD 0 false) (S 0) = S 1 := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
