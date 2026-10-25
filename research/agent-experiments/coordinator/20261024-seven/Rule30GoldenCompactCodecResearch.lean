import Rule30GoldenPackedBitsResearch

/-! A whole decoder state as one integer, with disjoint fields. The four
projection lemmas are valid without bounds on the input integers. -/

namespace Rule30GoldenCompactCodecResearch

def mask (n : Nat) : Nat := 2^n-1

def encode (A B R Rm flags used : Nat) : Nat :=
  (R &&& mask A) ||| ((Rm &&& mask B) <<< A) |||
    ((flags &&& mask 6) <<< (A+B)) ||| (used <<< (A+B+6))

def getR (x A : Nat) : Nat := x &&& mask A
def getRm (x A B : Nat) : Nat := (x >>> A) &&& mask B
def getFlags (x A B : Nat) : Nat := (x >>> (A+B)) &&& mask 6
def getUsed (x A B : Nat) : Nat := x >>> (A+B+6)

theorem getR_bit (A B R Rm flags used i : Nat) (hi : i<A) :
    (getR (encode A B R Rm flags used) A).testBit i = R.testBit i := by
  have hA : ¬ A≤i := by omega
  have hB : ¬ A+B≤i := by omega
  have hC : ¬ A+B+6≤i := by omega
  simp [getR,encode,mask,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftLeft,hi,hA,hB,hC]

theorem getRm_bit (A B R Rm flags used i : Nat) (hi : i<B) :
    (getRm (encode A B R Rm flags used) A B).testBit i = Rm.testBit i := by
  have hA : ¬ A+i<A := by omega
  have hB : A≤A+i := by omega
  have hC : ¬ A+B≤A+i := by omega
  have hD : ¬ A+B+6≤A+i := by omega
  simp [getRm,encode,mask,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,Nat.testBit_shiftLeft,
    hi,hA,hB,hC,hD]

theorem getFlags_bit (A B R Rm flags used i : Nat) (hi : i<6) :
    (getFlags (encode A B R Rm flags used) A B).testBit i = flags.testBit i := by
  have hA : ¬ A+B+i<A := by omega
  have hB : A≤A+B+i := by omega
  have hC : A+B≤A+B+i := by omega
  have hD : ¬ A+B+6≤A+B+i := by omega
  have hE : A+B+i-A=B+i := by omega
  have hF : ¬ B+i<B := by omega
  have hmask : (63 : Nat).testBit i = true := by
    change (2^6-1 : Nat).testBit i = true
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hi
  simp [getFlags,encode,mask,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,Nat.testBit_shiftLeft,
    hmask,hA,hB,hC,hD,hE,hF]

theorem getUsed_bit (A B R Rm flags used i : Nat) :
    (getUsed (encode A B R Rm flags used) A B).testBit i = used.testBit i := by
  have hA : ¬ A+B+6+i<A := by omega
  have hB : A≤A+B+6+i := by omega
  have hC : A+B≤A+B+6+i := by omega
  have hD : A+B+6≤A+B+6+i := by omega
  have hE : A+B+6+i-A=B+6+i := by omega
  have hF : ¬ B+6+i<B := by omega
  have hG : A+B+6+i-(A+B)=6+i := by omega
  have hH : ¬ 6+i<6 := by omega
  have hmask : (63 : Nat).testBit (6+i) = false := by
    change (2^6-1 : Nat).testBit (6+i) = false
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_false hH
  simp [getUsed,encode,mask,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,Nat.testBit_shiftLeft,
    hA,hB,hC,hD,hE,hF,hG,hmask]

theorem getUsed_encode (A B R Rm flags used : Nat) : getUsed (encode A B R Rm flags used) A B = used :=
  Nat.eq_of_testBit_eq (getUsed_bit A B R Rm flags used)

theorem bits_congr {a b n : Nat} (h : ∀ i, i<n → a.testBit i=b.testBit i) :
    Rule30GoldenPackedBitsResearch.bits a n = Rule30GoldenPackedBitsResearch.bits b n := by
  unfold Rule30GoldenPackedBitsResearch.bits
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

end Rule30GoldenCompactCodecResearch
