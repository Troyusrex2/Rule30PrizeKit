module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110001Steps6Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step14 : preCheck K ((List.replicate N false ++ tail).getD 14 false) (Q 14) (Q 15) = true := by decide +kernel
theorem step15 : preCheck K ((List.replicate N false ++ tail).getD 15 false) (Q 15) (Q 16) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
