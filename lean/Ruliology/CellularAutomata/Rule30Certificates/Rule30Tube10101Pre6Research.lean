module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Pre5Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep12 : restrictedPreCheck 16 false Z (Q 13) (Q 12) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 13) (Q 12) Zstates = true)
theorem Qstep13 : restrictedPreCheck 16 false Z (Q 14) (Q 13) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 14) (Q 13) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
