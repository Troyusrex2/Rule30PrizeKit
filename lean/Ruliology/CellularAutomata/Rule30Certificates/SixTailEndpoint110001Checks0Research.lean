module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001DefsResearch
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Zzero : Z.testBit 0 = true := by decide +kernel
theorem Zfixed : image K false Z = Z := by decide +kernel
theorem p0 : preCheck K (tail.getD 0 false) (P 0) (P 1) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
