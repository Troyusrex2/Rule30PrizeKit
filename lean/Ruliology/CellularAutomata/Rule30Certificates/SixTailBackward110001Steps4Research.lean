module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110001Steps3Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
