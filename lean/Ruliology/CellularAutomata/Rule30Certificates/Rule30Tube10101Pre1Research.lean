module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Pre0Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep2 : restrictedPreCheck 16 false Z (Q 3) (Q 2) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 3) (Q 2) Zstates = true)
theorem Qstep3 : restrictedPreCheck 16 false Z (Q 4) (Q 3) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 4) (Q 3) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
