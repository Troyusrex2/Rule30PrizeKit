import Ruliology.CellularAutomata.Rule30ControlledResponse

/-! A limitation of the two sound terminal rewrites. Irreducible high caps
100 and 111 alternate forever under the controlled update, for every driver;
their lengths grow by one at each step. This is not a prize theorem. -/

namespace Rule30ResponseGrowthResearch

def Q (a : Nat) : Nat := a ^^^ ((a >>> 1) ||| (a >>> 2))

def head (b : Bool) (a : Nat) : Bool := xor b (a.testBit 0 || a.testBit 1)

def packedStep (b : Bool) (a : Nat) : Nat := 2*Q a + (head b a).toNat

def packedRun (c : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => a
  | t+1 => packedStep (c t) (packedRun c a t)

def Cap (a n : Nat) : Prop := a >>> n = 4 ∨ a >>> n = 7

def TerminalReducible (a : Nat) : Prop := ∃ n, a >>> n = 5 ∨ a >>> n = 6

theorem Q_shift (a n : Nat) : Q a >>> n = Q (a >>> n) := by
  simp only [Q, Nat.shiftRight_xor_distrib, Nat.shiftRight_or_distrib,
    ← Nat.shiftRight_add]
  simp only [Nat.add_comm]

theorem packedStep_drop_head (b : Bool) (a : Nat) : packedStep b a >>> 1 = Q a := by
  rw [Nat.shiftRight_eq_div_pow]
  have hb : (head b a).toNat < 2 := by cases head b a <;> decide
  unfold packedStep
  omega

theorem packedStep_cap {a n : Nat} (ha : Cap a n) (b : Bool) :
    Cap (packedStep b a) (n+1) := by
  unfold Cap at *
  rw [show n+1=1+n by omega, Nat.shiftRight_add, packedStep_drop_head, Q_shift]
  rcases ha with ha | ha
  · rw [ha]; right; decide +kernel
  · rw [ha]; left; decide +kernel

theorem packedRun_cap {a n : Nat} (ha : Cap a n) (c : Nat → Bool) (t : Nat) :
    Cap (packedRun c a t) (n+t) := by
  induction t with
  | zero => simpa only [packedRun, Nat.add_zero] using ha
  | succ t ih => simpa only [packedRun, Nat.add_assoc] using packedStep_cap ih (c t)

theorem highThree_log2 {a n : Nat} (ha : 4 ≤ a >>> n ∧ a >>> n < 8) :
    a.log2 = n+2 := by
  have hnz : a >>> n ≠ 0 := by omega
  have hlog : (a >>> n).log2 = 2 := (Nat.log2_eq_iff hnz).mpr ha
  have hbit := Nat.testBit_log2 hnz
  rw [hlog, Nat.testBit_shiftRight] at hbit
  have hzero : a >>> (n+3) = 0 := by
    rw [Nat.shiftRight_add]
    exact Nat.shiftRight_eq_zero _ _ ha.2
  have hlt : a < 2^(n+3) :=
    Nat.lt_of_div_eq_zero (Nat.two_pow_pos _) (by rwa [← Nat.shiftRight_eq_div_pow])
  have anz : a ≠ 0 := by intro hz; rw [hz, Nat.zero_testBit] at hbit; cases hbit
  apply (Nat.log2_eq_iff anz).mpr
  constructor
  · apply Nat.le_of_not_gt
    intro h
    have hf := Nat.testBit_lt_two_pow h
    rw [hbit] at hf
    cases hf
  · simpa only [Nat.add_assoc] using hlt

theorem cap_log2 {a n : Nat} (ha : Cap a n) : a.log2 = n+2 := by
  apply highThree_log2
  rcases ha with ha | ha <;> rw [ha] <;> decide

theorem cap_irreducible {a n : Nat} (ha : Cap a n) : ¬ TerminalReducible a := by
  rintro ⟨k,hk⟩
  have han := cap_log2 ha
  have hak : a.log2 = k+2 := by
    apply highThree_log2
    rcases hk with hk | hk <;> rw [hk] <;> decide
  have he : k = n := by omega
  subst k
  rcases ha with ha | ha <;> rcases hk with hk | hk <;> omega

/-- At every time, no instance of either terminal rewrite can apply. -/
theorem run_irreducible {a n : Nat} (ha : Cap a n) (c : Nat → Bool) (t : Nat) :
    ¬ TerminalReducible (packedRun c a t) := cap_irreducible (packedRun_cap ha c t)

/-- Exact growth is independent of the input, even for a constant input. -/
theorem run_log2 {a n : Nat} (ha : Cap a n) (c : Nat → Bool) (t : Nat) :
    (packedRun c a t).log2 = n+t+2 := cap_log2 (packedRun_cap ha c t)

theorem seven_cap : Cap 7 0 := by right; rfl

theorem seven_unbounded (c : Nat → Bool) :
    ∀ N, ∃ t, N < (packedRun c 7 t).log2 := by
  intro N
  refine ⟨N+1, ?_⟩
  rw [run_log2 seven_cap]
  omega

theorem packedStep_or (b : Bool) (a : Nat) :
    packedStep b a = (Q a <<< 1) ||| (head b a).toNat := by
  have hb : (head b a).toNat < 2^1 := by cases head b a <;> decide
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]
  unfold packedStep
  omega

theorem packedStep_sound (b : Bool) (a k : Nat) :
    (packedStep b a).testBit k =
      Ruliology.CellularAutomata.Rule30ControlledResponse.step b a.testBit k := by
  rw [packedStep_or]
  cases k with
  | zero =>
      change ((Q a <<< 1) ||| (head b a).toNat).testBit 0 = head b a
      cases h : head b a <;> simp [h]
  | succ k =>
      simp [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_bool_toNat, Q,
        Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight,
        Ruliology.CellularAutomata.Rule30ControlledResponse.step,
        Ruliology.CellularAutomata.Rule30ControlledResponse.prepend,
        Ruliology.CellularAutomata.Rule30ControlledResponse.diagonal, Nat.add_comm]

theorem packedRun_sound (c : Nat → Bool) (a t k : Nat) :
    (packedRun c a t).testBit k =
      Ruliology.CellularAutomata.Rule30ControlledResponse.run c a.testBit t k := by
  induction t generalizing k with
  | zero => rfl
  | succ t ih =>
      rw [packedRun, packedStep_sound]
      have hf : (packedRun c a t).testBit =
          Ruliology.CellularAutomata.Rule30ControlledResponse.run c a.testBit t :=
        funext ih
      rw [hf]
      rfl

/-- A constant observed output coexists with unbounded irreducible states.
Thus this normalizer's size cannot serve as observed-output complexity. -/
theorem constant_output_unbounded_states :
    (∀ t, (packedRun (fun _ => false) 7 t).testBit 0 = true) ∧
    (∀ t, ¬ TerminalReducible (packedRun (fun _ => false) 7 t)) ∧
    (∀ N, ∃ t, N < (packedRun (fun _ => false) 7 t).log2) := by
  refine ⟨?_, fun t => run_irreducible seven_cap _ t, seven_unbounded _⟩
  intro t
  rw [packedRun_sound]
  exact Ruliology.CellularAutomata.Rule30ControlledResponse.zero_driver_head
    (Nat.testBit 7) (by decide) t

end Rule30ResponseGrowthResearch
