import Rule30GoldenBudgetDFSResearch

/-! Compact integer storage of single-lane anti-diagonals. Packing preserves
the projected Boolean cells; no assumption about discarded higher bits is
needed. This module alone makes no termination claim. -/

namespace Rule30GoldenPackedBitsResearch

def pack : List Nat → Nat
  | [] => 0
  | a::as => (a.testBit 0).toNat ||| (pack as <<< 1)

def bits (a n : Nat) : List Nat := (List.range n).map (fun i => (a.testBit i).toNat)

theorem bits_length (a n : Nat) : (bits a n).length = n := by simp [bits]

theorem pack_testBit (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    (pack xs).testBit i = (xs.getD i 0).testBit 0 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => cases h : a.testBit 0 <;> simp [pack,h,Nat.testBit_or,Nat.testBit_shiftLeft]
    | succ i =>
      have ht : i < as.length := by simpa using hi
      have hx := ih i ht
      have h1 : (1 : Nat).testBit (i+1) = false := by rw [Nat.testBit_add_one];simp
      cases h : a.testBit 0 <;> simp [pack,h,Nat.testBit_or,Nat.testBit_shiftLeft,hx,h1]

theorem bits_getD (a n i : Nat) (hi : i < n) :
    ((bits a n).getD i 0).testBit 0 = a.testBit i := by
  cases h : a.testBit i <;> simp [bits,List.getD_eq_getElem?_getD,hi,h]

theorem bits_pack_project (xs : List Nat) :
    (bits (pack xs) xs.length).map (fun a => a.testBit 0) = xs.map (fun a => a.testBit 0) := by
  apply List.ext_getElem
  · simp [bits_length]
  · intro i hi hj
    have ht : i < xs.length := by simpa only [List.length_map,bits_length] using hi
    have h := (bits_getD (pack xs) xs.length i ht).trans (pack_testBit xs i ht)
    have hbl : i < (bits (pack xs) xs.length).length := by rw [bits_length];exact ht
    have hL : (bits (pack xs) xs.length).getD i 0 = (bits (pack xs) xs.length)[i] := by
      simp [List.getD_eq_getElem?_getD,hbl]
    have hR : xs.getD i 0 = xs[i] := by simp [List.getD_eq_getElem?_getD,ht]
    rw [hL,hR] at h
    simpa only [List.getElem_map] using h

end Rule30GoldenPackedBitsResearch
