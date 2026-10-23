module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110001Steps0Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
