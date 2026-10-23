module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110001DefsResearch
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
