import Rule30StripeTraceResearch

/-! The seed's low-bit class has no nontrivial stripe ambiguity, at any
center or time. This does not prove completeness of the stripe relation,
separation of equal infinite traces, or the prize theorem. -/

namespace Rule30NormalizationMachineResearch.SeedBoundary

open Ruliology.CellularAutomata Rule30Jen Rule30Prize

def SeedLow (a : Nat) : Prop := a.testBit 0 = true ∧ a.testBit 1 = a.testBit 2

theorem seedLow_one : SeedLow 1 := by unfold SeedLow; decide +kernel

theorem Phi_bit_zero (a : Nat) : (Phi a).testBit 0 = a.testBit 0 := by
  rw [Phi_testBit]
  simp [before]

theorem phiRows_bit_zero (a t : Nat) : (phiRows a t).testBit 0 = a.testBit 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [phiRows, Phi_bit_zero] using ih

theorem seedLow_phi {a : Nat} (ha : SeedLow a) : SeedLow (Phi a) := by
  constructor
  · simpa only [Phi_bit_zero] using ha.1
  · simp [Phi_testBit, before, ha.1, ha.2]

theorem seedLow_phiRows {a : Nat} (ha : SeedLow a) (t : Nat) : SeedLow (phiRows a t) := by
  induction t with
  | zero => exact ha
  | succ t ih => exact seedLow_phi ih

theorem seedLow_tailRun_three {a : Nat} (ha : SeedLow a) : tailRun a 3 = 4 := by
  change tailNext (tailNext (tailNext 0 (a.testBit 0)) (a.testBit 1)) (a.testBit 2) = 4
  rw [ha.1, ha.2]
  cases a.testBit 2 <;> rfl

theorem seedLow_tailRun_dead {a : Nat} (ha : SeedLow a) :
    ∀ n, 3 ≤ n → tailRun a n = 4 := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      intro hn
      by_cases hn3 : 3 ≤ n
      · rw [tailRun, ih hn3]
        rfl
      · have hn2 : n = 2 := by omega
        subst n
        exact seedLow_tailRun_three ha

/-- The only stripe-related partner of a row in the seed's invariant low-bit
class is that row itself. Width and center are unrestricted. -/
theorem seedLow_stripe_trivial {a b c : Nat} (ha : SeedLow a)
    (h : StripeRelated a b c) : a = b := by
  rcases h with he | ⟨j, _, hsa, _, haj, hbj, hza, hzb, hh⟩
  · exact he
  · have hj : j ≤ 1 := by
      by_cases hj : j ≤ 1
      · exact hj
      · have ht := (tailRun_accept_iff a (j+1)).mpr hsa
        rw [seedLow_tailRun_dead ha (j+1) (by omega)] at ht
        rcases ht with ht | ht <;> omega
    have hj0 : j = 0 := by
      by_cases hj0 : j = 0
      · exact hj0
      · have hj1 : j = 1 := by omega
        subst j
        have h12 := ha.2
        rw [haj, hza] at h12
        cases h12
    subst j
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi0 : i = 0
    · subst i
      exact haj.trans hbj.symm
    · by_cases hi1 : i = 1
      · subst i
        exact hza.trans hzb.symm
      · exact hh i (by omega)

theorem stripe_symm {a b c : Nat} (h : StripeRelated a b c) : StripeRelated b a c := by
  rcases h with he | ⟨j, hj, hsa, hsb, haj, hbj, hza, hzb, hh⟩
  · exact Or.inl he.symm
  · exact Or.inr ⟨j, hj, hsb, hsa, hbj, haj, hzb, hza, fun i hi => (hh i hi).symm⟩

theorem seedLow_even_disjoint {a b c : Nat} (ha : SeedLow a) (hb : b.testBit 0 = false) :
    ¬ StripeRelated a b c := by
  intro h
  have he := congrArg (fun x : Nat => x.testBit 0) (seedLow_stripe_trivial ha h)
  rw [ha.1, hb] at he
  cases he

theorem seedLow_even_never_stripe {a b : Nat} (ha : SeedLow a) (hb : b.testBit 0 = false)
    (t c : Nat) : ¬ StripeRelated (phiRows a t) (phiRows b t) c := by
  exact seedLow_even_disjoint (seedLow_phiRows ha t) ((phiRows_bit_zero b t).trans hb)

theorem positive_shift_even (a p : Nat) (hp : 0 < p) : (a <<< p).testBit 0 = false := by
  rw [Nat.testBit_shiftLeft]
  simp only [show decide (p ≤ 0) = false from decide_eq_false (by omega), Bool.false_and]

/-- These are the aligned finite rows that an eventual period would compare.
They cannot enter the proved stripe relation at any future time. This is not
a proof that their center traces eventually differ. -/
theorem period_pair_never_stripe (T P u c : Nat) (hP : 0 < P) :
    ¬ StripeRelated (phiRows ((phiRows 1 T) <<< P) u) (phiRows 1 (T+P+u)) c := by
  have h := seedLow_even_never_stripe (seedLow_phiRows seedLow_one (T+P))
    (positive_shift_even (phiRows 1 T) P hP) u c
  rw [← phiRows_add] at h
  exact fun hh => h (stripe_symm hh)

/-! The physical-coordinate bridge below is the earlier moving-frame proof,
specialized to `phiRows`; it is included rather than assumed. -/

def readAt (a : Nat) (p : Int) : Bool := if p < 0 then false else a.testBit p.toNat

theorem Phi_bit_bounds (a k : Nat) :
    (Phi a).testBit k = xor (a.testBit k)
      ((if 1 ≤ k then a.testBit (k-1) else false) ||
       (if 2 ≤ k then a.testBit (k-2) else false)) := by
  simp [Phi, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]

theorem readAt_Phi (a : Nat) (p : Int) :
    readAt (Phi a) p = rule (readAt a p) (readAt a (p-1)) (readAt a (p-2)) := by
  by_cases hp : p < 0
  · simp [readAt, hp, show p-1 < 0 by omega, show p-2 < 0 by omega, rule]
  · obtain ⟨k, rfl⟩ : ∃ k : Nat, (k : Int) = p := ⟨p.toNat, by omega⟩
    rw [readAt, ite_eq_right (by omega), Int.toNat_natCast, Phi_bit_bounds]
    simp only [readAt, rule]
    by_cases h1 : 1 ≤ k
    · by_cases h2 : 2 ≤ k
      · simp only [ite_eq_left h1, ite_eq_left h2,
          ite_eq_right (show ¬ (k : Int)-2 < 0 by omega),
          ite_eq_right (show ¬ (k : Int)-1 < 0 by omega),
          ite_eq_right (show ¬ (k : Int) < 0 by omega),
          show ((k : Int)-2).toNat = k-2 by omega,
          show ((k : Int)-1).toNat = k-1 by omega, Int.toNat_natCast]
      · have : k = 1 := by omega
        subst k
        simp
    · have : k = 0 := by omega
      subst k
      simp

theorem right_white : ∀ (t : Nat) (p : Int), (t : Int) < p → cell t p = false
  | 0, p, hp => by simp [cell, show p ≠ 0 by omega]
  | t+1, p, hp => by
      rw [cell, right_white t (p-1) (by omega), right_white t p (by omega),
        right_white t (p+1) (by omega)]
      rfl

theorem seedRows_sound (t : Nat) (p : Int) :
    readAt (phiRows 1 t) p = cell t (t-p) := by
  induction t generalizing p with
  | zero =>
      by_cases hp : p < 0
      · simp [readAt, hp, cell, show p ≠ 0 by omega]
      · simp only [phiRows, readAt, ite_eq_right hp, cell, Int.ofNat_zero]
        change (Bool.toNat true).testBit p.toNat = decide (0-p = 0)
        rw [Nat.testBit_bool_toNat]
        simp [show p.toNat = 0 ↔ p = 0 by omega]
  | succ t ih =>
      by_cases hp : p < 0
      · rw [readAt, ite_eq_left hp, right_white _ _ (by omega)]
      · rw [phiRows, readAt_Phi, ih, ih, ih, cell]
        congr 1 <;> congr 1 <;> omega

theorem seedRows_bit (t k : Nat) :
    (phiRows 1 t).testBit k = cell t ((t : Int)-k) := by
  simpa [readAt, show ¬ (k : Int) < 0 by omega] using seedRows_sound t (k : Int)

theorem center_is_phi (t : Nat) : center t = (phiRows 1 t).testBit t := by
  simpa [center] using (seedRows_bit t t).symm

theorem shift_commute (a p q : Nat) : (a <<< p) <<< q = (a <<< q) <<< p := by
  simp only [Nat.shiftLeft_eq]
  exact Nat.mul_right_comm _ _ _

theorem Phi_shift (a p : Nat) : Phi (a <<< p) = (Phi a) <<< p := by
  unfold Phi
  rw [Nat.shiftLeft_xor_distrib, Nat.shiftLeft_or_distrib,
    shift_commute a p 1, shift_commute a p 2]

theorem phiRows_shift (a p u : Nat) : phiRows (a <<< p) u = (phiRows a u) <<< p := by
  induction u with
  | zero => rfl
  | succ u ih => rw [phiRows, ih, Phi_shift]; rfl

theorem aligned_seed_read (T P u : Nat) :
    (phiRows ((phiRows 1 T) <<< P) u).testBit (T+P+u) = center (T+u) := by
  rw [phiRows_shift, Nat.testBit_shiftLeft,
    decide_eq_true (show P ≤ T+P+u by omega), Bool.true_and,
    show T+P+u-P = T+u by omega, ← phiRows_add, ← center_is_phi]

theorem period_pair_left_outside (T P : Nat) (hP : 0 < P) :
    ∃ k, (phiRows 1 (T+P)).testBit k = true ∧ ZerosFrom ((phiRows 1 T) <<< P) k := by
  refine ⟨2*(T+P), ?_, ?_⟩
  · rw [seedRows_bit,
      show ((T+P : Nat) : Int) - ((2*(T+P) : Nat) : Int) = -((T+P : Nat) : Int) by omega,
      cell_left_edge]
  · intro i hi
    rw [Nat.testBit_shiftLeft, decide_eq_true (show P ≤ i by omega), Bool.true_and,
      seedRows_bit]
    exact cell_eq_false_of_lt T _ (by omega)

theorem shifted_seed_positive (T P : Nat) : 0 < (phiRows 1 T) <<< P := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hbit : ((phiRows 1 T) <<< P).testBit P = true := by
    rw [Nat.testBit_shiftLeft]
    simpa only [Nat.le_refl, decide_true, Bool.true_and, Nat.sub_self] using
      (seedLow_phiRows seedLow_one T).1
  rw [hz, Nat.zero_testBit] at hbit
  cases hbit

def SameTrace (a b c : Nat) : Prop :=
  ∀ u, (phiRows a u).testBit (c+u) = (phiRows b u).testBit (c+u)

/-- OPEN. Only even starts versus seed-low starts extending farther left are
covered by this proposed sufficient condition. No separation proof is supplied. -/
def SeedLowEvenLeftSeparation : Prop :=
  ∀ a b c : Nat, 0 < a → a.testBit 0 = false → SeedLow b →
    (∃ k, b.testBit k = true ∧ ZerosFrom a k) → ¬ SameTrace a b c

theorem periodic_center_forces_seed_even_collision (hper : EventuallyPeriodic center) :
    ∃ a b c : Nat, 0 < a ∧ a.testBit 0 = false ∧ SeedLow b ∧
      (∃ k, b.testBit k = true ∧ ZerosFrom a k) ∧ SameTrace a b c := by
  obtain ⟨T, P, hP, hEq⟩ := hper
  refine ⟨(phiRows 1 T) <<< P, phiRows 1 (T+P), T+P,
    shifted_seed_positive T P, positive_shift_even _ P hP,
    seedLow_phiRows seedLow_one (T+P), period_pair_left_outside T P hP, ?_⟩
  intro u
  rw [aligned_seed_read, ← phiRows_add, ← center_is_phi]
  have he := hEq (T+u) (by omega)
  simpa only [show T+u+P = T+P+u by omega] using he.symm

/-- Conditional implication to the exact official statement. The hypothesis
`SeedLowEvenLeftSeparation` is OPEN; this is not a proof of Problem 1. -/
theorem problem1_of_seedLow_even_left_separation (h : SeedLowEvenLeftSeparation) :
    Rule30Prize.Problem1 := by
  intro hp
  obtain ⟨a, b, c, hap, ha, hb, hout, ht⟩ := periodic_center_forces_seed_even_collision hp
  exact h a b c hap ha hb hout ht

end Rule30NormalizationMachineResearch.SeedBoundary
