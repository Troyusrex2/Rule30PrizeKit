module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Force2Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qforce15 : colConst 16 (Z &&& Q 15) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 15) false Zstates = true)
theorem Qforce16 : colConst 16 (Z &&& Q 16) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 16) false Zstates = true)
theorem Qforce17 : colConst 16 (Z &&& Q 17) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 17) false Zstates = true)
theorem Qforce18 : colConst 16 (Z &&& Q 18) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 18) false Zstates = true)
theorem Qforce19 : colConst 16 (Z &&& Q 19) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 19) false Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
