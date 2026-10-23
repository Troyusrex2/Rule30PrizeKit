module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100001Steps3Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step16 : preCheck K ((List.replicate N false ++ tail).getD 16 false) (Q 16) (Q 17) = true := by decide +kernel
theorem step17 : preCheck K ((List.replicate N false ++ tail).getD 17 false) (Q 17) (Q 18) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001
