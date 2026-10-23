module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110001Steps2Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
