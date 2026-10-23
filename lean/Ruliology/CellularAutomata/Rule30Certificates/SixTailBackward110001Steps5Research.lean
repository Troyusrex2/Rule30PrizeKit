module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110001Steps4Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
theorem step11 : preCheck K ((List.replicate N false ++ tail).getD 11 false) (Q 11) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
