module

public import Ruliology.CellularAutomata.Rule30WhitePad10111

/-! Width-eight envelope certificates for arbitrary reset mixtures: all white gaps at least nine,
with a gap of at least seventeen. The soundness bridge is in `Rule30ResetMixtures`. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ResetMixtures

open Rule30StripCertificates Rule30WhitePad10111

def A0 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def A1 : Nat := 0xa868b02aa120302920298022a128222ba868a02b2120102220298062a028222b
def A2 : Nat := 0x2868302aa120302920290022a128222b2868202b2120102220290062a028222b
def A3 : Nat := 0x2028202a20202028202800222020202a2028202a20200022202800222020202a
def G : Nat := 0x2020000000202000202000000020202020200000002000000020000000202020

theorem full_A0 : fullSet 8 = A0 := by decide +kernel

theorem entry0 : wp 9 (image 8 true A0) &&& A1 = wp 9 (image 8 true A0) := by decide +kernel
theorem closed1 : image 8 false A1 &&& A1 = image 8 false A1 := by decide +kernel
theorem entry1 : wp 9 (image 8 true A1) &&& A2 = wp 9 (image 8 true A1) := by decide +kernel
theorem closed2 : image 8 false A2 &&& A2 = image 8 false A2 := by decide +kernel
theorem entry2 : wp 9 (image 8 true A2) &&& A3 = wp 9 (image 8 true A2) := by decide +kernel
theorem closed3 : image 8 false A3 &&& A3 = image 8 false A3 := by decide +kernel
theorem entry3 : wp 9 (image 8 true A3) &&& A3 = wp 9 (image 8 true A3) := by decide +kernel
theorem nested21 : A2 &&& A1 = A2 := by decide +kernel
theorem nested32 : A3 &&& A2 = A3 := by decide +kernel
/-- The reset: one gap of length at least seventeen sends the captured set into `G`. -/
theorem reset17 : wp 17 (image 8 true A3) &&& G = wp 17 (image 8 true A3) := by decide +kernel
theorem closedG : image 8 false G &&& G = image 8 false G := by decide +kernel
theorem entryG : wp 9 (image 8 true G) &&& G = wp 9 (image 8 true G) := by decide +kernel

theorem white0 : colConst 8 (image 8 true G) false = true := by decide +kernel
theorem white1 : colConst 8 (wp 1 (image 8 true G)) false = true := by decide +kernel
theorem white2 : wp 2 (image 8 true G) &&& oddMask = wp 2 (image 8 true G) := by decide +kernel

end Ruliology.CellularAutomata.Rule30ResetMixtures
