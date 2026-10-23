module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101DefsResearch

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Zzero : Z.testBit 0 = true := by decide +kernel
theorem Zfixed : image 16 false Z = Z := by decide +kernel
theorem Sstep0 : image 16 (tail.getD 0 false) (S 0) = S 1 := by decide +kernel
theorem Sstep1 : image 16 (tail.getD 1 false) (S 1) = S 2 := by decide +kernel
theorem Sstep2 : image 16 (tail.getD 2 false) (S 2) = S 3 := by decide +kernel
theorem Sstep3 : image 16 (tail.getD 3 false) (S 3) = S 4 := by decide +kernel
theorem Sstep4 : image 16 (tail.getD 4 false) (S 4) = S 5 := by decide +kernel
theorem Szero : S 0 = Z := rfl
theorem Qend : Q 24 = 1 := rfl
theorem Pend : P 5 = 1 := rfl
theorem Qstart : Q 0 = P 0 := rfl
end Ruliology.CellularAutomata.Rule30Tube10101Research
