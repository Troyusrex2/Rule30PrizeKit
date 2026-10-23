module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101SparseDefsResearch

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qforce0 : colConst 16 (Z &&& Q 0) true = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 0) true Zstates = true)
theorem Qforce1 : colConst 16 (Z &&& Q 1) true = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 1) true Zstates = true)
theorem Qforce2 : colConst 16 (Z &&& Q 2) true = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 2) true Zstates = true)
theorem Qforce3 : colConst 16 (Z &&& Q 3) true = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 3) true Zstates = true)
theorem Qforce4 : colConst 16 (Z &&& Q 4) true = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 4) true Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
