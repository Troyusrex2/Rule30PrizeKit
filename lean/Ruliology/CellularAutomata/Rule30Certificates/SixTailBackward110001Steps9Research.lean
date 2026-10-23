module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110001Steps8Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step18 : preCheck K ((List.replicate N false ++ tail).getD 18 false) (Q 18) (Q 19) = true := by decide +kernel
theorem step19 : preCheck K ((List.replicate N false ++ tail).getD 19 false) (Q 19) (Q 20) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
