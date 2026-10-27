module

public import Ruliology.CellularAutomata.Rule30Certificates.TrapPeriod21
public import Ruliology.CellularAutomata.Rule30EtherThreeTrap

/-!
# The 001 trap has no full period21 right extension

An actual right-half history entering a correctly aligned `t001` state cannot
have temporal period21 in every column. The proof retains the full Rule30
recurrence, checks every trap state's full head value, and normalizes any entry
label to zero. A kernel-checked closed predecessor cycle supplies the obstruction.
-/

@[expose] public section

/-! A physical bridge for the label-zero 001-trap head pair.
The period21 hypothesis applies to EVERY right column at ALL times. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata.Rule30TrapPeriod21.Physical
open Ruliology.CellularAutomata.Rule30Period21Profiles Ruliology.CellularAutomata.Rule30Certificates.TrapPeriod21
open Ruliology.CellularAutomata Rule30Ether Rule30StripCertificates

def encode (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => encode f n ||| ((f n).toNat <<< n)

theorem testBit_encode (f : Nat → Bool) :
    ∀ n k, (encode f n).testBit k = (decide (k < n) && f k)
  | 0, k => by simp [encode]
  | n + 1, k => by
    rw [encode, Nat.testBit_or, testBit_encode f n k, Nat.testBit_shiftLeft,
      testBit_toNat]
    by_cases hk : k < n
    · simp [hk, show k < n + 1 by omega, show ¬ n ≤ k by omega]
    · by_cases he : k = n
      · subst k; simp
      · simp [hk, show ¬ k < n + 1 by omega, show k - n ≠ 0 by omega]

theorem encode_lt (f : Nat → Bool) (n : Nat) : encode f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by
    rw [testBit_encode]
    simp [show ¬ k < n by omega]

theorem testBit_rotate (a : Nat) (ha : a < modulus) (k : Nat) (hk : k < 21) :
    (rotate a).testBit k = a.testBit ((k + 1) % 21) := by
  rw [rotate, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    testBit_toNat]
  by_cases he : k = 20
  · subst k
    have h21 : a.testBit 21 = false := Nat.testBit_lt_two_pow ha
    simp [h21]
  · have hlt : k < 20 := by omega
    simp [show ¬ 20 ≤ k by omega, Nat.mod_eq_of_lt (show k + 1 < 21 by omega),
      Nat.add_comm]

def column (F : Nat → Nat → Bool) (j : Nat) : Nat := encode (fun t => F t j) 21

theorem column_lt (F : Nat → Nat → Bool) (j : Nat) : column F j < modulus :=
  encode_lt _ _

theorem column_bit (F : Nat → Nat → Bool) (j k : Nat) (hk : k < 21) :
    (column F j).testBit k = F k j := by
  rw [column, testBit_encode]
  simp [hk]

theorem column_step (F : Nat → Nat → Bool) (hF : IsR30 F)
    (hper : ∀ t j, F (t + 21) j = F t j) (j : Nat) :
    step (column F (j + 1), column F (j + 2)) = (column F j, column F (j + 1)) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq
    intro k
    change ((rotate (column F (j + 1)) ^^^
      (column F (j + 1) ||| column F (j + 2))) % 2 ^ 21).testBit k =
      (column F j).testBit k
    rw [Nat.testBit_mod_two_pow]
    by_cases hk : k < 21
    · rw [decide_eq_true hk, Bool.true_and, Nat.testBit_xor, Nat.testBit_or,
        testBit_rotate _ (column_lt _ _) _ hk,
        column_bit _ _ _ (Nat.mod_lt _ (by decide)),
        column_bit _ _ _ hk, column_bit _ _ _ hk, column_bit _ _ _ hk]
      have ht : F ((k + 1) % 21) (j + 1) = F (k + 1) (j + 1) := by
        by_cases he : k = 20
        · subst k
          simpa using (hper 0 (j + 1)).symm
        · rw [Nat.mod_eq_of_lt (by omega)]
      rw [ht, hF k j]
      change xor (xor (F k j) (F k (j + 1) || F k (j + 2)))
        (F k (j + 1) || F k (j + 2)) = F k j
      cases F k j <;> cases (F k (j + 1) || F k (j + 2)) <;> rfl
    · rw [decide_eq_false hk, Bool.false_and, column, testBit_encode]
      simp [hk]
  · rfl

theorem column_eq_literal (F : Nat → Nat → Bool) (j a : Nat)
    (ha : a < modulus) (h : ∀ k, k < 21 → F k j = a.testBit k) : column F j = a := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 21
  · rw [column_bit _ _ _ hk, h k hk]
  · have hb : a.testBit k = false := by
      rw [← Nat.mod_eq_of_lt ha]
      change (a % 2 ^ 21).testBit k = false
      rw [Nat.testBit_mod_two_pow]
      simp [hk]
    rw [column, testBit_encode, hb]
    simp [hk]

/-- No full actual right-half history has common period21 and the specified label-zero
trap head pair. No finite-support premise or unrestricted exterior input is substituted. -/
theorem no_period21_history (F : Nat → Nat → Bool) (hF : IsR30 F)
    (hper : ∀ t j, F (t + 21) j = F t j)
    (h0 : ∀ k, k < 21 → F k 0 = (1198372 : Nat).testBit k)
    (h1 : ∀ k, k < 21 → F k 1 = (1591590 : Nat).testBit k) : False := by
  let s : Nat → State := fun j => (column F j, column F (j + 1))
  apply no_bounded_inverse s
  · apply Prod.ext
    · exact column_eq_literal F 0 1198372 (by decide) h0
    · exact column_eq_literal F 1 1591590 (by decide) h1
  · intro j
    exact ⟨column_lt _ _, column_lt _ _⟩
  · intro j
    simpa only [s, Nat.add_assoc] using column_step F hF hper j

end Ruliology.CellularAutomata.Rule30TrapPeriod21.Physical


/-! The named t001 bridge: full head projection, including black driver phases,
and normalization of any correctly entered label to zero. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata.Rule30TrapPeriod21
open Ruliology.CellularAutomata Rule30Ether Rule30EtherThree

theorem full_head_check : allBelowT (fun i =>
    (t001.st i).testBit 0 == (1591590 : Nat).testBit (t001.lab i)) t001.n = true := by
  decide +kernel

theorem full_head {i : Nat} (hi : i < t001.n) :
    (t001.st i).testBit 0 = (1591590 : Nat).testBit (t001.lab i) := by
  have := allBelowT_spec full_head_check i hi
  simpa only [beq_iff_eq] using this

theorem driver_check : allBelowT (fun k =>
    wordAt3 w001 k == (1198372 : Nat).testBit k) 21 = true := by
  decide +kernel

theorem driver_bits (k : Nat) (hk : k < 21) :
    wordAt3 w001 k = (1198372 : Nat).testBit k := by
  have := allBelowT_spec driver_check k hk
  simpa only [beq_iff_eq] using this

/-- Any actual right-half history that enters a correctly aligned t001 state cannot
have common temporal period21 on the whole right half. This includes every entry label;
it does not assert absorption or rule out an aperiodic exterior. -/
theorem no_period21_trapped (F : Nat → Nat → Bool) (hF : IsR30 F)
    (hper : ∀ t j, F (t + 21) j = F t j)
    (T : Nat) (hc : ∀ t, T ≤ t → F t 0 = wordAt3 t001.w (t - T))
    (t1 i : Nat) (ht1 : T ≤ t1) (hi : i < t001.n)
    (hph : (t1 - T) % 3 = t001.lab i % 3)
    (hr : EncF F t001.b t1 0 (t001.st i)) : False := by
  have inv := PTrap.invariant t001 t001_check hF T hc t1 i ht1 hi hph hr
  have hl : t001.lab i < 21 := (PTrap.step t001 t001_check hi false).2.2.2.1
  let q := 21 - t001.lab i
  let b := t1 + q
  have hq : t001.lab i + q = 21 := by dsimp [q]; omega
  let H : Nat → Nat → Bool := fun t p => F (b + t) p
  have hH : IsR30 H := by
    intro t p
    dsimp [H]
    simpa only [Nat.add_assoc] using hF (b + t) p
  have hHp : ∀ t j, H (t + 21) j = H t j := by
    intro t j
    dsimp [H]
    simpa only [Nat.add_assoc] using hper (b + t) j
  apply Ruliology.CellularAutomata.Rule30TrapPeriod21.Physical.no_period21_history H hH hHp
  · intro k hk
    change F (b + k) 0 = _
    rw [hc (b + k) (by dsimp [b]; omega)]
    have hmod : (b + k - T) % 3 = k % 3 := by dsimp [b]; omega
    change wordAt3 w001 (b + k - T) = _
    rw [show wordAt3 w001 (b + k - T) = wordAt3 w001 k by
      unfold wordAt3
      rw [hmod]]
    exact driver_bits k hk
  · intro k hk
    change F (b + k) 1 = _
    obtain ⟨j, hj, hrow, hlabel⟩ := inv (q + k)
    have hlabel' : t001.lab j = k := by
      change t001.lab j = (t001.lab i + (q + k)) % 21 at hlabel
      rw [show t001.lab i + (q + k) = 21 + k by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hk] at hlabel
      exact hlabel
    calc F (b + k) 1 = (t001.st j).testBit 0 := by
           simpa only [b, Nat.add_assoc] using (encF_head hrow (by decide)).symm
         _ = (1591590 : Nat).testBit (t001.lab j) := full_head hj
         _ = (1591590 : Nat).testBit k := by rw [hlabel']

end Ruliology.CellularAutomata.Rule30TrapPeriod21
