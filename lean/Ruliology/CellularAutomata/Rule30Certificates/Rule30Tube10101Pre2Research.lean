module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Pre1Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep4 : restrictedPreCheck 16 false Z (Q 5) (Q 4) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 5) (Q 4) Zstates = true)
theorem Qstep5 : restrictedPreCheck 16 false Z (Q 6) (Q 5) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 6) (Q 5) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
