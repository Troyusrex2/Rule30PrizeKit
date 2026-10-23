module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Pre6Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep14 : restrictedPreCheck 16 false Z (Q 15) (Q 14) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 15) (Q 14) Zstates = true)
theorem Qstep15 : restrictedPreCheck 16 false Z (Q 16) (Q 15) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 16) (Q 15) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
