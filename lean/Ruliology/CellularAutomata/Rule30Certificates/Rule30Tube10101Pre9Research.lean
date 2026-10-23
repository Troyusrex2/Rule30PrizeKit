module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Pre8Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep18 : restrictedPreCheck 16 false Z (Q 19) (Q 18) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 19) (Q 18) Zstates = true)
theorem Qstep19 : restrictedPreCheck 16 false Z (Q 20) (Q 19) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 20) (Q 19) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
