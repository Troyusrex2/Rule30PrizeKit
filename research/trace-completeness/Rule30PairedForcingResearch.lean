import Rule30StripeTraceResearch

/-! Exact forcing of a paired XOR difference and the center's masking gate.
These identities do not assume the paired difference is a Rule 30 history,
and do not establish trace completeness. -/

namespace Rule30NormalizationMachineResearch

theorem local_polarization : ∀ al ac ar bl bc br : Bool,
    xor (xor al (ac || ar)) (xor bl (bc || br)) =
      xor (xor (xor al bl) (xor ac bc || xor ar br))
        (xor (ac && br) (ar && bc)) := by decide +kernel

theorem before_xor (a b i k : Nat) : before (a ^^^ b) i k =
    xor (before a i k) (before b i k) := by
  by_cases h : k < i
  · simp [before,h,Nat.testBit_xor]
  · simp [before,h]

def crossDefect (a b i : Nat) : Bool :=
  xor (before a i 0 && before b i 1) (before a i 1 && before b i 0)

theorem paired_difference_step (a b i : Nat) :
    (Phi a ^^^ Phi b).testBit i = xor ((Phi (a ^^^ b)).testBit i) (crossDefect a b i) := by
  simp only [Nat.testBit_xor,Phi_testBit,before_xor,crossDefect]
  exact local_polarization _ _ _ _ _ _

theorem local_center_gate : ∀ al ac ar bl bc br : Bool,
    ac = bc → xor al (ac || ar) = xor bl (bc || br) →
      xor al bl = (!ac && xor ar br) := by decide +kernel

theorem same_center_gate (a b c : Nat) (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    xor (a.testBit (c+1)) (b.testBit (c+1)) =
      (!a.testBit c && xor (before a (c+1) 1) (before b (c+1) 1)) := by
  apply local_center_gate _ _ _ _ _ _ h0
  simpa only [Phi_testBit,before_succ_zero] using h1

end Rule30NormalizationMachineResearch
