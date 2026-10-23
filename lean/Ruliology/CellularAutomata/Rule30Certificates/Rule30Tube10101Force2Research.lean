module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Force1Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qforce10 : colConst 16 (Z &&& Q 10) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 10) false Zstates = true)
theorem Qforce11 : colConst 16 (Z &&& Q 11) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 11) false Zstates = true)
theorem Qforce12 : colConst 16 (Z &&& Q 12) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 12) false Zstates = true)
theorem Qforce13 : colConst 16 (Z &&& Q 13) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 13) false Zstates = true)
theorem Qforce14 : colConst 16 (Z &&& Q 14) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 14) false Zstates = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
