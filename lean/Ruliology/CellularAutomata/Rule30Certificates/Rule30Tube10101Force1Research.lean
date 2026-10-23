module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Force0Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qforce5 : colConst 16 (Z &&& Q 5) true = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 5) true Zstates = true)
theorem Qforce6 : colConst 16 (Z &&& Q 6) true = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 6) true Zstates = true)
theorem Qforce7 : colConst 16 (Z &&& Q 7) true = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 7) true Zstates = true)
theorem Qforce8 : colConst 16 (Z &&& Q 8) true = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 8) true Zstates = true)
theorem Qforce9 : colConst 16 (Z &&& Q 9) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 9) false Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
