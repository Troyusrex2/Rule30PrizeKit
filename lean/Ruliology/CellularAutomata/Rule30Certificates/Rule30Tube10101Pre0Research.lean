module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101SparseDefsResearch

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qstep0 : restrictedPreCheck 16 false Z (Q 1) (Q 0) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 1) (Q 0) Zstates = true)
theorem Qstep1 : restrictedPreCheck 16 false Z (Q 2) (Q 1) = true := by
  exact restricted_of_sparse Zmask (by decide +kernel : sparsePreCheck 16 false (Q 2) (Q 1) Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
