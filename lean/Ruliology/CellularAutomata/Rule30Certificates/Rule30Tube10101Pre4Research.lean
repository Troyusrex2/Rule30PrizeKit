module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Pre3Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep8 : restrictedPreCheck 16 false Z (Q 9) (Q 8) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 9) (Q 8) Zstates = true)
theorem Qstep9 : restrictedPreCheck 16 false Z (Q 10) (Q 9) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 10) (Q 9) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
