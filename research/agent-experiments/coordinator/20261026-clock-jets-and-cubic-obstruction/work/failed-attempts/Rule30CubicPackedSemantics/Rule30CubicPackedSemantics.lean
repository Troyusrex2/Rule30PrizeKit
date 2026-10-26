module
public import Rule30CubicCertificateData

/-! Generic semantics for the packed certificate calculations. -/
@[expose] public section
namespace Rule30CubicPackedSemantics
open Rule30CubicCertificateData
open Rule30ReaderCanonicalResearch
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

def bitXor (x : Nat) : Nat → Bool
  | 0 => false
  | n+1 => xor (x.testBit n) (bitXor x n)

theorem parity_semantics (n x : Nat) : parity n x=bitXor x 64 := by
  simp [parity, bitXor, Nat.ble_eq_true_of_le (Nat.zero_le _),
    Nat.testBit_xor, Nat.testBit_shiftRight, Bool.xor_assoc,
    Bool.xor_comm, Bool.xor_left_comm]

theorem word_length (x n : Nat) : (word x n).length=n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [word,List.length_cons,ih]

theorem word_getElem (x n i : Nat) (hi : i<n) :
    (word x n)[i]'(by rw [word_length];exact hi)=x.testBit i := by
  induction n generalizing x i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa [word,Nat.testBit_shiftRight,Nat.add_comm] using
        ih (x>>>1) i (by omega)

theorem packed_bit (x i : Nat) (hi : i<width) :
    (stepPacked x).testBit i = xor (x.testBit i)
      ((decide (1≤i) && x.testBit (i-1)) ||
       (decide (2≤i) && x.testBit (i-2))) := by
  simp [stepPacked, Nat.testBit_mod_two_pow,hi,Nat.testBit_xor,
    Nat.testBit_or,Nat.testBit_shiftLeft]

end Rule30CubicPackedSemantics
