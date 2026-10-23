module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Pre2Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep6 : restrictedPreCheck 16 false Z (Q 7) (Q 6) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 7) (Q 6) Zstates = true)
theorem Qstep7 : restrictedPreCheck 16 false Z (Q 8) (Q 7) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 8) (Q 7) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
