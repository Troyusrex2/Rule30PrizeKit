module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Force3Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates Rule30SparsePreimageResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Qforce20 : colConst 16 (Z &&& Q 20) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 20) false Zstates = true)
theorem Qforce21 : colConst 16 (Z &&& Q 21) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 21) false Zstates = true)
theorem Qforce22 : colConst 16 (Z &&& Q 22) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 22) false Zstates = true)
theorem Qforce23 : colConst 16 (Z &&& Q 23) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 23) false Zstates = true)
theorem Qforce24 : colConst 16 (Z &&& Q 24) false = true := by
  exact colConst_inter_of_sparse Zmask (by decide +kernel : sparseColConst (Q 24) false Zstates = true)
theorem Pforce1 : colConst 16 (S 1 &&& P 1) false = true := by
  exact colConst_inter_of_sparse S1mask (by decide +kernel : sparseColConst (P 1) false S1states = true)
theorem Pforce3 : colConst 16 (S 3 &&& P 3) false = true := by
  exact colConst_inter_of_sparse S3mask (by decide +kernel : sparseColConst (P 3) false S3states = true)
end Ruliology.CellularAutomata.Rule30Tube10101Research
