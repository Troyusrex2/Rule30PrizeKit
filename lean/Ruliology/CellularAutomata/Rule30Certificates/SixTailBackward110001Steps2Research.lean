module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110001Steps1Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
