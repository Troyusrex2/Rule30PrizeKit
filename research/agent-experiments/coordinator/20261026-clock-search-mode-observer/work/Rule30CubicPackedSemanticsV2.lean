module
public import Rule30CubicCertificateData

/-! Generic semantics for the packed certificate calculations. -/
@[expose] public section
namespace Rule30CubicPackedSemanticsV2
open Rule30CubicCertificateData
open Rule30ReaderCanonicalResearch
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem xorList_perm {α : Type} {xs ys : List α} (h : xs.Perm ys)
    (f : α → Bool) : xorList xs f=xorList ys f := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [xorList,ih]
  | swap a b xs => simp only [xorList]; cases f a <;> cases f b <;> cases xorList xs f <;> rfl
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

def bitOrder : List Nat := [0, 32, 16, 48, 8, 40, 24, 56, 4, 36, 20, 52, 12, 44, 28, 60, 2, 34, 18, 50, 10, 42, 26, 58, 6, 38, 22, 54, 14, 46, 30, 62, 1, 33, 17, 49, 9, 41, 25, 57, 5, 37, 21, 53, 13, 45, 29, 61, 3, 35, 19, 51, 11, 43, 27, 59, 7, 39, 23, 55, 15, 47, 31, 63]
theorem bitOrder_perm : bitOrder.Perm (List.range 64) := by decide +kernel

theorem parity_expanded (n x : Nat) :
    parity n x=xorList bitOrder (fun i => x.testBit i) := by
  simp only [parity, xorList, bitOrder, Nat.ble_eq_true_of_le (Nat.zero_le _),
    ite_true, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.xor_assoc,
    Bool.xor_false, Nat.reduceAdd, Nat.add_zero]

theorem parity_semantics (n x : Nat) :
    parity n x=xorList (List.range 64) (fun i => x.testBit i) := by
  exact (parity_expanded n x).trans (xorList_perm bitOrder_perm _)

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

def bget (xs : List Bool) (i : Nat) : Bool := xs[i]?.getD false

theorem word_bget (x n i : Nat) (hi : i<n) : bget (word x n) i=x.testBit i := by
  simp [bget, List.getElem?_eq_getElem, word_length,hi,word_getElem]

theorem change_length (xs : List Bool) (p q : Bool) :
    (singleChange p q xs).length=xs.length := by
  induction xs generalizing p q with
  | nil => rfl
  | cons x xs ih => simp only [singleChange,List.length_cons,ih]

theorem change_bit (xs : List Bool) (p q : Bool) (i : Nat) (hi : i<xs.length) :
    bget (singleChange p q xs) i = xor (bget xs i)
      ((if i=0 then p else bget xs (i-1)) ||
       (if i=0 then q else if i=1 then p else bget xs (i-2))) := by
  induction xs generalizing p q i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have ht := ih x p i (by simpa using hi)
      cases i with
      | zero => simpa [bget,singleChange] using ht
      | succ i => cases i <;> simpa [bget,singleChange,Nat.add_assoc] using ht

theorem stepPacked_matches_rule (x i : Nat) (hi : i<width) :
    bget (singleStep (word x width)) i=(stepPacked x).testBit i := by
  rw [singleStep,change_bit _ false false i (by rw[word_length];exact hi),
    word_bget x width i hi,packed_bit x i hi]
  cases i with
  | zero => simp
  | succ i =>
    cases i with
    | zero => simp [word_bget,show 0<width by decide +kernel]
    | succ i =>
      have h₁ : i+1<width := by omega
      have h₀ : i<width := by omega
      simp [word_bget x width (i+1) h₁,word_bget x width i h₀]

end Rule30CubicPackedSemanticsV2
