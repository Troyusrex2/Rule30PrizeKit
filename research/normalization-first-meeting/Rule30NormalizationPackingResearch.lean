import Rule30NormalizationWindowResearch

/-! Exact bounds and bit-field packing for the transducer.
Companion modules prove the actual-row and stripe-relation correspondences. -/

namespace Rule30NormalizationMachineResearch

structure View where
  e0 : Nat
  e1 : Nat
  e2 : Nat
  ha : Nat
  hb : Nat
  code : Nat

def View.Valid (v : View) : Prop := v.e0 < 200 ∧ v.e1 < 200 ∧ v.e2 < 200 ∧
  v.ha < 16 ∧ v.hb < 16 ∧ v.code ≤ 4

def View.encode (v : View) : Nat := v.e0 + (v.e1 <<< 8) + (v.e2 <<< 16) +
  (v.ha <<< 24) + (v.hb <<< 28) + (v.code <<< 32)

theorem View.decode_encode (v : View) (h : v.Valid) :
    v.encode % 256 = v.e0 ∧ (v.encode >>> 8) % 256 = v.e1 ∧
    (v.encode >>> 16) % 256 = v.e2 ∧ (v.encode >>> 24) % 16 = v.ha ∧
    (v.encode >>> 28) % 16 = v.hb ∧ v.encode >>> 32 = v.code := by
  obtain ⟨h0,h1,h2,ha,hb,hc⟩ := h
  unfold View.encode
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  repeat' constructor <;> omega

def symbol (a b marker : Bool) : Nat := a.toNat + 2 * b.toNat + 4 * marker.toNat

theorem symbol_lt (a b marker : Bool) : symbol a b marker < 8 := by
  cases a <;> cases b <;> cases marker <;> decide

theorem symbol_bits (a b marker : Bool) :
    (symbol a b marker).testBit 0 = a ∧ (symbol a b marker).testBit 1 = b ∧
    (symbol a b marker).testBit 2 = marker := by
  cases a <;> cases b <;> cases marker <;> decide

theorem tailNext_lt (s : Nat) (b : Bool) : tailNext s b < 5 := by
  unfold tailNext
  split <;> decide

theorem bool_nat_le (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem relStep_lt (e : Nat) (a b allow : Bool) : relStep e a b allow < 200 := by
  let ta := tailNext ((e / 8) / 5) a
  let tb := tailNext ((e / 8) % 5) b
  let valid := (e.testBit 0 && (a == b)) || (e.testBit 1 && !a && !b)
  let pending := allow && a && b && (ta == 1 || ta == 3) && (tb == 1 || tb == 3)
  let ident := e.testBit 2 && (a == b)
  change 8 * (5 * ta + tb) + 4 * ident.toNat + 2 * pending.toNat + valid.toNat < 200
  have ht : ta < 5 := tailNext_lt _ _
  have hu : tb < 5 := tailNext_lt _ _
  have hi := bool_nat_le ident
  have hp := bool_nat_le pending
  have hv := bool_nat_le valid
  omega

end Rule30NormalizationMachineResearch
