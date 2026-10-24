import Rule30NormalizationMachineResearch

/-! Exact integer/stream correspondence for the machine's two Rule 30 layers.
Companion modules interpret the tail language and stripe relation.
Numerical-normalizer equivalence and infinite-trace completeness remain open. -/

namespace Rule30NormalizationMachineResearch

def Phi (a : Nat) : Nat := a ^^^ ((a <<< 1) ||| (a <<< 2))

def before (a i k : Nat) : Bool := decide (k < i) && a.testBit (i - (k+1))

theorem Phi_testBit (a i : Nat) :
    (Phi a).testBit i = xor (a.testBit i) (before a i 0 || before a i 1) := by
  have h1 : decide (1 ≤ i) = decide (0 < i) := by
    by_cases h : 1 ≤ i
    · have h' : 0 < i := by omega
      simp [h, h']
    · have h' : ¬ 0 < i := by omega
      simp [h, h']
  have h2 : decide (2 ≤ i) = decide (1 < i) := by
    by_cases h : 2 ≤ i
    · have h' : 1 < i := by omega
      simp [h, h']
    · have h' : ¬ 1 < i := by omega
      simp [h, h']
  simp only [Phi, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft, before,
    h1, h2, Nat.zero_add]

def pack4 (b0 b1 b2 b3 : Bool) : Nat :=
  b0.toNat ||| (b1.toNat <<< 1) ||| (b2.toNat <<< 2) ||| (b3.toNat <<< 3)

theorem pack4_bit0 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 0 = b0 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_bit1 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 1 = b1 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_bit2 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 2 = b2 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_bit3 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 3 = b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_lt (b0 b1 b2 b3 : Bool) : pack4 b0 b1 b2 b3 < 16 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_shift (b0 b1 b2 b3 x : Bool) :
    pack4 x b0 b1 b2 = (2 * pack4 b0 b1 b2 b3 + x.toNat) % 16 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases x <;> decide

def history (a i : Nat) : Nat := pack4 (before a i 0) (before a i 1)
  (before a i 2) (before a i 3)

theorem history_lt (a i : Nat) : history a i < 16 := pack4_lt _ _ _ _

theorem history_bit0 (a i : Nat) : (history a i).testBit 0 = before a i 0 := pack4_bit0 _ _ _ _
theorem history_bit1 (a i : Nat) : (history a i).testBit 1 = before a i 1 := pack4_bit1 _ _ _ _
theorem history_bit2 (a i : Nat) : (history a i).testBit 2 = before a i 2 := pack4_bit2 _ _ _ _
theorem history_bit3 (a i : Nat) : (history a i).testBit 3 = before a i 3 := pack4_bit3 _ _ _ _

theorem before_succ_zero (a i : Nat) : before a (i+1) 0 = a.testBit i := by
  simp [before]

theorem before_succ_succ (a i k : Nat) : before a (i+1) (k+1) = before a i k := by
  by_cases h : k < i
  · have h' : k+1 < i+1 := by omega
    have hi : (i+1)-(k+1+1) = i-(k+1) := by omega
    simp [before, h, h', hi]
  · have h' : ¬ k+1 < i+1 := by omega
    simp [before, h, h']

theorem history_zero (a : Nat) : history a 0 = 0 := by simp [history, before, pack4]

theorem history_succ (a i : Nat) :
    history a (i+1) = (2 * history a i + (a.testBit i).toNat) % 16 := by
  unfold history
  rw [before_succ_zero, before_succ_succ a i 0, before_succ_succ a i 1,
    before_succ_succ a i 2]
  exact pack4_shift _ _ _ _ _

theorem before_of_lt (a i k : Nat) (hk : k < i) :
    before a i k = a.testBit (i-(k+1)) := by simp [before, hk]

theorem before_shift (a i k l : Nat) (hk : k < i) :
    before a (i-(k+1)) l = before a i (k+l+1) := by
  by_cases hl : l < i-(k+1)
  · have hr : k+l+1 < i := by omega
    simp only [before, hl, hr, decide_true, Bool.true_and]
    congr 1
    omega
  · have hr : ¬ k+l+1 < i := by omega
    simp [before, hl, hr]

theorem before_Phi (a i k : Nat) :
    before (Phi a) i k = xor (before a i k)
      (before a i (k+1) || before a i (k+2)) := by
  by_cases hk : k < i
  · rw [before_of_lt _ _ _ hk, Phi_testBit,
      before_shift a i k 0 hk, before_shift a i k 1 hk, before_of_lt a i k hk]
  · have h1 : ¬ k+1 < i := by omega
    have h2 : ¬ k+2 < i := by omega
    simp [before, hk, h1, h2]

theorem first_exact (a i : Nat) :
    (Phi a).testBit i = first (history a i) (a.testBit i) := by
  rw [Phi_testBit]
  simp only [first, history_bit0, history_bit1]

theorem second_exact (a i : Nat) :
    (Phi (Phi a)).testBit i = second (history a i) (a.testBit i) := by
  rw [Phi_testBit, first_exact, before_Phi, before_Phi]
  simp only [second, first, history_bit0, history_bit1, history_bit2, history_bit3,
    Nat.zero_add]

end Rule30NormalizationMachineResearch
