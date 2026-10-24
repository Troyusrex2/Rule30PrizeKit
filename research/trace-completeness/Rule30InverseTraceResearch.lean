import Rule30StripeTraceResearch

/-! Exact arbitrary-width inverse trace codes. No zero-tail, height recovery,
EdgeObservable or prize theorem is asserted. -/

namespace Rule30NormalizationMachineResearch.InverseTrace

theorem xor_common : ∀ p q r : Bool,
    xor (xor p r) (xor q r) = xor p q := by decide +kernel

theorem xor_solve : ∀ p q r : Bool, xor p q = r → p = xor r q := by decide +kernel

theorem xor_twice : ∀ p q : Bool, xor (xor p q) q = p := by decide +kernel

theorem xor_false_iff : ∀ p q : Bool, xor p q = false ↔ p = q := by decide +kernel

theorem prefixEq_before {a b n : Nat} (h : PrefixEq a b n) (i k : Nat) (hi : i ≤ n) :
    before a i k = before b i k := by
  by_cases hk : k < i
  · simp only [before,hk,decide_true,Bool.true_and]
    exact h _ (by omega)
  · simp [before,hk]

theorem prefixEq_phi {a b n : Nat} (h : PrefixEq a b n) : PrefixEq (Phi a) (Phi b) n := by
  intro i hi
  rw [Phi_testBit,Phi_testBit,h i hi,
    prefixEq_before h i 0 (by omega),prefixEq_before h i 1 (by omega)]

theorem prefixEq_phiRows {a b n : Nat} (h : PrefixEq a b n) (t : Nat) :
    PrefixEq (phiRows a t) (phiRows b t) n := by
  induction t with
  | zero => exact h
  | succ t ih => exact prefixEq_phi ih

theorem bit_xor_phi {a b n : Nat} (h : PrefixEq a b n) :
    xor ((Phi a).testBit n) ((Phi b).testBit n) = xor (a.testBit n) (b.testBit n) := by
  rw [Phi_testBit,Phi_testBit,prefixEq_before h n 0 (by omega),
    prefixEq_before h n 1 (by omega)]
  exact xor_common _ _ _

theorem bit_xor_phiRows {a b n : Nat} (h : PrefixEq a b n) (t : Nat) :
    xor ((phiRows a t).testBit n) ((phiRows b t).testBit n) =
      xor (a.testBit n) (b.testBit n) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      exact (bit_xor_phi (prefixEq_phiRows h t)).trans ih

theorem bit_response {a b n : Nat} (h : PrefixEq a b n) (hb : b.testBit n = false) (t : Nat) :
    (phiRows a t).testBit n = xor (a.testBit n) ((phiRows b t).testBit n) := by
  apply xor_solve
  simpa only [hb,Bool.xor_false] using bit_xor_phiRows h t

def extendPrefix (a n : Nat) (bit : Bool) : Nat := a ||| if bit then 2^n else 0

theorem extendPrefix_bit (a n i : Nat) (bit : Bool) :
    (extendPrefix a n bit).testBit i = (a.testBit i || (bit && decide (n = i))) := by
  cases bit <;> simp [extendPrefix,Nat.testBit_or,Nat.testBit_two_pow]

theorem extendPrefix_prefix (a n : Nat) (bit : Bool) : PrefixEq (extendPrefix a n bit) a n := by
  intro i hi
  rw [extendPrefix_bit]
  simp [show n ≠ i by omega]

theorem extendPrefix_top {a n : Nat} (ha : a < 2^n) (bit : Bool) :
    (extendPrefix a n bit).testBit n = bit := by
  rw [extendPrefix_bit,Nat.testBit_lt_two_pow ha]
  simp

theorem extendPrefix_lt {a n : Nat} (ha : a < 2^n) (bit : Bool) :
    extendPrefix a n bit < 2^(n+1) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [extendPrefix_bit]
  have hx : a < 2^i := Nat.lt_of_lt_of_le ha
    (Nat.pow_le_pow_of_le (by decide) (by omega))
  simp [Nat.testBit_lt_two_pow hx,show n ≠ i by omega]

def inversePrefix (target : Nat → Bool) (c right : Nat) : Nat → Nat
  | 0 => 0
  | n+1 =>
      let old := inversePrefix target c right n
      let pick := if n < c then right.testBit n else
        xor (target (n-c)) ((phiRows old (n-c)).testBit n)
      extendPrefix old n pick

theorem inversePrefix_lt (target : Nat → Bool) (c right n : Nat) :
    inversePrefix target c right n < 2^n := by
  induction n with
  | zero => simp [inversePrefix]
  | succ n ih => exact extendPrefix_lt ih _

theorem inversePrefix_right (target : Nat → Bool) (c right n i : Nat)
    (hic : i < c) (hin : i < n) :
    (inversePrefix target c right n).testBit i = right.testBit i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      rw [inversePrefix]
      by_cases hi : i < n
      · exact (extendPrefix_prefix _ _ _ i hi).trans (ih i hic hi)
      · have he : i = n := by omega
        subst i
        rw [extendPrefix_top (inversePrefix_lt target c right n)]
        simp only [ite_eq_left hic]

/-- The constructed prefix realizes every requested observation whose initial
leftmost dependency lies inside that prefix. Both width and center are arbitrary. -/
theorem inversePrefix_realizes (target : Nat → Bool) (c right n t : Nat)
    (ht : c+t < n) : (phiRows (inversePrefix target c right n) t).testBit (c+t) = target t := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
      let old := inversePrefix target c right n
      let pick := if n < c then right.testBit n else
        xor (target (n-c)) ((phiRows old (n-c)).testBit n)
      change (phiRows (extendPrefix old n pick) t).testBit (c+t) = target t
      have ha : old < 2^n := inversePrefix_lt target c right n
      have hp := extendPrefix_prefix old n pick
      by_cases hi : c+t < n
      · exact (prefixEq_phiRows hp t _ hi).trans (ih t hi)
      · have he : c+t = n := by omega
        rw [he]
        calc
          (phiRows (extendPrefix old n pick) t).testBit n =
              xor ((extendPrefix old n pick).testBit n) ((phiRows old t).testBit n) :=
            bit_response hp (Nat.testBit_lt_two_pow ha) t
          _ = xor pick ((phiRows old t).testBit n) := by rw [extendPrefix_top ha]
          _ = target t := by
            have hc : ¬ n < c := by omega
            have hh : n-c = t := by omega
            dsimp only [pick]
            rw [ite_eq_right hc,hh]
            exact xor_twice _ _

/-- A right prefix together with the corresponding finite center trace is an
injective code for rows below 2^n. This assumes the right prefixes agree; it
does not recover the right prefix or prove EdgeObservable. -/
theorem finite_trace_code_injective {a b c n : Nat} (ha : a < 2^n) (hb : b < 2^n)
    (hr : ∀ i, i < c → i < n → a.testBit i = b.testBit i)
    (ht : ∀ t, c+t < n → (phiRows a t).testBit (c+t) = (phiRows b t).testBit (c+t)) : a = b := by
  have low : ∀ i, i < n → a.testBit i = b.testBit i := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
        intro hin
        by_cases hic : i < c
        · exact hr i hic hin
        · have hp : PrefixEq a b i := fun j hj => ih j hj (by omega)
          have he : c+(i-c) = i := by omega
          have obs : (phiRows a (i-c)).testBit i = (phiRows b (i-c)).testBit i := by
            simpa only [he] using ht (i-c) (by omega)
          have hx := bit_xor_phiRows hp (i-c)
          apply (xor_false_iff _ _).mp
          rw [← hx,obs]
          cases (phiRows b (i-c)).testBit i <;> rfl
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact low i hi
  · have pa : a < 2^i := Nat.lt_of_lt_of_le ha
      (Nat.pow_le_pow_of_le (by decide) (by omega))
    have pb : b < 2^i := Nat.lt_of_lt_of_le hb
      (Nat.pow_le_pow_of_le (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow pa,Nat.testBit_lt_two_pow pb]

theorem inversePrefix_unique (target : Nat → Bool) (c right n a : Nat) (ha : a < 2^n)
    (hr : ∀ i, i < c → i < n → a.testBit i = right.testBit i)
    (ht : ∀ t, c+t < n → (phiRows a t).testBit (c+t) = target t) :
    a = inversePrefix target c right n := by
  apply finite_trace_code_injective ha (inversePrefix_lt target c right n)
  · intro i hic hin
    exact (hr i hic hin).trans (inversePrefix_right target c right n i hic hin).symm
  · intro t htn
    exact (ht t htn).trans (inversePrefix_realizes target c right n t htn).symm

end Rule30NormalizationMachineResearch.InverseTrace
