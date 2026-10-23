module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111101Steps2Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111101
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step12 : preCheck K ((List.replicate N false ++ tail).getD 12 false) (Q 12) (Q 13) = true := by decide +kernel
theorem step13 : preCheck K ((List.replicate N false ++ tail).getD 13 false) (Q 13) (Q 14) = true := by decide +kernel
theorem step14 : preCheck K ((List.replicate N false ++ tail).getD 14 false) (Q 14) (Q 15) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111101
