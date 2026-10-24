import Ruliology.CellularAutomata.Rule30Prize

/-! Finite ancestry exploration. This module establishes the exact growth of
the packed finite row and refutes a short ancestry-detection horizon. It does
not establish that infinite traces determine ancestry or solve Problem 1. -/

namespace Rule30AncestryResearch

-- The same packed right-to-left frame used by Rule30StripeMeeting. Keeping
-- these three elementary definitions local avoids importing its certificate.
def Phi (a : Nat) : Nat := a ^^^ ((a <<< 1) ||| (a <<< 2))

def phiRows (a : Nat) : Nat → Nat
  | 0 => a
  | t+1 => Phi (phiRows a t)

def SameCenterPrefix (a b c n : Nat) : Prop :=
  ∀ t, t < n → (phiRows a t).testBit (c+t) = (phiRows b t).testBit (c+t)

theorem bit_above_log2 (a k : Nat) (hk : a.log2 < k) : a.testBit k = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le Nat.lt_log2_self
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem Phi_top_bit {a : Nat} (ha : a ≠ 0) :
    (Phi a).testBit (a.log2+2) = true := by
  have h0 := bit_above_log2 a (a.log2+2) (by omega)
  have h1 := bit_above_log2 a (a.log2+1) (by omega)
  have h2 := Nat.testBit_log2 ha
  simp [Phi, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft,
    h0, h1, h2]

theorem Phi_ne_zero {a : Nat} (ha : a ≠ 0) : Phi a ≠ 0 := by
  intro hz
  have h := Phi_top_bit ha
  rw [hz, Nat.zero_testBit] at h
  cases h

theorem Phi_log2 {a : Nat} (ha : a ≠ 0) : (Phi a).log2 = a.log2+2 := by
  apply (Nat.log2_eq_iff (Phi_ne_zero ha)).mpr
  constructor
  · apply Nat.le_of_not_gt
    intro hlt
    have h := Nat.testBit_lt_two_pow hlt
    rw [Phi_top_bit ha] at h
    cases h
  · apply Nat.lt_pow_two_of_testBit
    intro k hk
    have h0 := bit_above_log2 a k (by omega)
    have h1 := bit_above_log2 a (k-1) (by omega)
    have h2 := bit_above_log2 a (k-2) (by omega)
    simp [Phi, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft, h0, h1, h2]

theorem phiRows_ne_zero {a : Nat} (ha : a ≠ 0) (t : Nat) : phiRows a t ≠ 0 := by
  induction t with
  | zero => exact ha
  | succ t ih => exact Phi_ne_zero ih

theorem phiRows_log2 {a : Nat} (ha : a ≠ 0) (t : Nat) :
    (phiRows a t).log2 = a.log2+2*t := by
  induction t with
  | zero => simp [phiRows]
  | succ t ih =>
      rw [phiRows, Phi_log2 (phiRows_ne_zero ha t), ih]
      omega

/-- Every finite positive prehistory has a depth bounded by the current row.
This is a support calculation, not a way to recover that depth from a trace. -/
theorem finite_ancestry_bound {a b t : Nat} (hb : b ≠ 0) (h : phiRows b t = a) :
    2*t ≤ a.log2 := by
  rw [← h, phiRows_log2 hb]
  omega

theorem parent49 : Phi 15 = 49 := by decide +kernel

theorem no_parent42_check :
    (List.range 16).all (fun a => Phi a != 42) = true := by decide +kernel

/-- Failure to have a finite predecessor is established for every natural
input, rather than inferred from a bounded search. -/
theorem no_parent42 : ¬ ∃ a : Nat, Phi a = 42 := by
  rintro ⟨a, ha⟩
  have hne : a ≠ 0 := by
    intro hzero
    subst a
    have : Phi 0 = 0 := by rfl
    omega
  have hlog := Phi_log2 hne
  rw [ha] at hlog
  have h42 : Nat.log2 42 = 5 := by decide +kernel
  rw [h42] at hlog
  have halog : a.log2 = 3 := by omega
  have hlt : a < 16 := by
    have h : a < 2^(a.log2+1) := Nat.lt_log2_self
    simpa only [halog] using h
  have hb := List.all_eq_true.mp no_parent42_check a (List.mem_range.mpr hlt)
  simpa [ha] using hb

theorem pair17_check : (List.range 17).all (fun t =>
    (phiRows 49 t).testBit (2+t) == (phiRows 42 t).testBit (2+t)) = true := by
  decide +kernel

theorem pair17_prefix : SameCenterPrefix 49 42 2 17 := by
  intro t ht
  exact beq_iff_eq.mp (List.all_eq_true.mp pair17_check t (List.mem_range.mpr ht))

theorem pair17_difference :
    (phiRows 49 17).testBit 19 ≠ (phiRows 42 17).testBit 19 := by decide +kernel

theorem pair17_same_edge : Nat.log2 49 = 5 ∧ Nat.log2 42 = 5 := by decide +kernel

/-- Even finite-predecessor membership cannot be recovered in `2*n+2`
observations for all n-bit rows. This does not refute infinite-trace recovery. -/
theorem short_ancestry_horizon_counterexample :
    ∃ a b n c : Nat, 0 < a ∧ 0 < b ∧ a < 2^n ∧ b < 2^n ∧ c < n ∧
      SameCenterPrefix a b c (2*n+2) ∧
      (∃ x : Nat, Phi x = a) ∧ ¬ (∃ x : Nat, Phi x = b) := by
  refine ⟨49,42,6,2,by decide,by decide,by decide,by decide,by decide,?_,
    ⟨15,parent49⟩,no_parent42⟩
  intro t ht
  exact pair17_prefix t (by omega)

end Rule30AncestryResearch
