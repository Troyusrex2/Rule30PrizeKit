module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Pre7Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep16 : restrictedPreCheck 16 false Z (Q 17) (Q 16) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 17) (Q 16) Zstates = true)
theorem Qstep17 : restrictedPreCheck 16 false Z (Q 18) (Q 17) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 18) (Q 17) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
