module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks2Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem s1 : image K (tail.getD 1 false) (S 1) = S 2 := by decide +kernel
theorem s2 : image K (tail.getD 2 false) (S 2) = S 3 := by decide +kernel
theorem s3 : image K (tail.getD 3 false) (S 3) = S 4 := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
