module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Pre9Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep20 : restrictedPreCheck 16 false Z (Q 21) (Q 20) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 21) (Q 20) Zstates = true)
theorem Qstep21 : restrictedPreCheck 16 false Z (Q 22) (Q 21) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 22) (Q 21) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
