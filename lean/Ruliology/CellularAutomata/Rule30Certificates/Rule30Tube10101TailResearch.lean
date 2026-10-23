module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101DefsResearch

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Pstep0 : preCheck 16 (tail.getD 0 false) (P 0) (P 1) = true := by decide +kernel
theorem Pstep1 : preCheck 16 (tail.getD 1 false) (P 1) (P 2) = true := by decide +kernel
theorem Pstep2 : preCheck 16 (tail.getD 2 false) (P 2) (P 3) = true := by decide +kernel
theorem Pstep3 : preCheck 16 (tail.getD 3 false) (P 3) (P 4) = true := by decide +kernel
theorem Pstep4 : preCheck 16 (tail.getD 4 false) (P 4) (P 5) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Tube10101Research
