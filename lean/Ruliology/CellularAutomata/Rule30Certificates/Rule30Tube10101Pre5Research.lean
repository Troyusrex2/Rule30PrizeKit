module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Pre4Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep10 : restrictedPreCheck 16 false Z (Q 11) (Q 10) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 11) (Q 10) Zstates = true)
theorem Qstep11 : restrictedPreCheck 16 false Z (Q 12) (Q 11) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 12) (Q 11) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
