module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift

/-! Period lifting for the triangular front-window permutation.
Existence of a period does not assert the required white-witness checks. -/

@[expose] public section

/-! Contributed by Troy Lowry and OpenAI Codex. Builds on the catalog's
stripe-front and bit-sliced lane methods. Does not prove Q01 or Problem 1. -/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontPeriod
open Ruliology.CellularAutomata
open Rule30ZeroBoundaryStripeFront Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift

theorem fstep_top_flip (K a p : Nat) (hp : p < 2) :
    fstep (K+1) (a ^^^ 2^K) p = (fstep (K+1) a p) ^^^ 2^K := by
  apply Nat.eq_of_testBit_eq
  intro i
  conv => rhs; rw [Nat.testBit_xor]
  rw [testBit_fstep (K+1) (a ^^^ 2^K) p i hp,
      testBit_fstep (K+1) a p i hp]
  simp only [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : i < K+1
  · rcases (show i < K ∨ i = K by omega) with hil | hiK
    · simp [hi, show K ≠ i by omega, show K ≠ i-1 by omega,
        show K ≠ i-2 by omega]
    · subst i
      rcases (show K = 0 ∨ K = 1 ∨ 2 ≤ K by omega) with rfl | rfl | hk
      · simp [Bool.xor_comm]
      · simp [Bool.xor_comm]
      · simp only [decide_eq_true hi, decide_true, Bool.true_and, Bool.xor_true,
          ite_eq_right (show K ≠ 0 by omega), ite_eq_right (show K ≠ 1 by omega),
          decide_eq_false (show K ≠ K-1 by omega),
          decide_eq_false (show K ≠ K-2 by omega), Bool.xor_false]
        cases a.testBit K <;> cases (a.testBit (K-1) || a.testBit (K-2)) <;> rfl
  · simp [hi, show K ≠ i by omega]

theorem orbit_phase_lt (K a p t : Nat) (hp : p < 2) :
    (orb K t (a,p)).2 < 2 := by
  cases t with
  | zero => exact hp
  | succ t => change 1-(orb K t (a,p)).2 < 2; omega

theorem orbit_top_flip (K a p t : Nat) (hp : p < 2) :
    orb (K+1) t (a ^^^ 2^K,p) =
      ((orb (K+1) t (a,p)).1 ^^^ 2^K, (orb (K+1) t (a,p)).2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [orb, fS, ih]
    rw [fstep_top_flip K _ _ (orbit_phase_lt _ _ _ _ hp)]

theorem fstep_bound (K a p : Nat) : fstep K a p < 2^K := by
  unfold fstep
  exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos K) (by decide))

theorem orbit_bound {K a p : Nat} (ha : a < 2^K) (t : Nat) :
    (orb K t (a,p)).1 < 2^K := by
  cases t with
  | zero => exact ha
  | succ t => exact fstep_bound _ _ _

theorem low_two_choices {K a b : Nat} (ha : a < 2^(K+1)) (hb : b < 2^(K+1))
    (h : LowEq K a b) : a = b ∨ a = b ^^^ 2^K := by
  by_cases he : a.testBit K = b.testBit K
  · left
    apply Nat.eq_of_testBit_eq
    intro i
    rcases (show i < K ∨ i = K ∨ K+1 ≤ i by omega) with hi | hiK | hi
    · exact h i hi
    · subst i; exact he
    · rw [Rule30ZeroBoundarySmall.testBit_ge_of_lt ha hi,
        Rule30ZeroBoundarySmall.testBit_ge_of_lt hb hi]
  · right
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    rcases (show i < K ∨ i = K ∨ K+1 ≤ i by omega) with hi | hiK | hi
    · rw [decide_eq_false (show K ≠ i by omega), Bool.xor_false]
      exact h i hi
    · subst i
      simp only [decide_true, Bool.xor_true]
      cases hA : a.testBit K <;> cases hB : b.testBit K <;> simp_all
    · rw [decide_eq_false (show K ≠ i by omega), Bool.xor_false,
        Rule30ZeroBoundarySmall.testBit_ge_of_lt ha hi,
        Rule30ZeroBoundarySmall.testBit_ge_of_lt hb hi]

/-- Every even return of the lower window yields a return after twice as many
steps in the one-bit-larger window. No certificate-success claim is included. -/
theorem double_period {K a b p L : Nat} (ha : a < 2^(K+1)) (hp : p < 2)
    (hinit : LowEq K a b) (hlo : orb K L (b,p) = (b,p)) :
    orb (K+1) (L+L) (a,p) = (a,p) := by
  have hpair := orbit_low (n := K) (K₁ := K+1) (K₂ := K)
    (a := a) (b := b) (p := p) (by omega) (Nat.le_refl _) hinit hp L
  rw [hlo] at hpair
  have hs : (orb (K+1) L (a,p)).2 = p := hpair.1
  have hl : LowEq K (orb (K+1) L (a,p)).1 a := by
    intro i hi
    exact (hpair.2.2 i hi).trans (hinit i hi).symm
  rcases low_two_choices (orbit_bound ha L) ha hl with he | he
  · have hr : orb (K+1) L (a,p) = (a,p) := Prod.ext he hs
    rw [orb_add, hr, hr]
  · have hr : orb (K+1) L (a,p) = (a ^^^ 2^K,p) := Prod.ext he hs
    rw [orb_add, hr, orbit_top_flip K a p L hp, hr]
    simp [Nat.xor_assoc]

/-- A uniform period bound for every nonempty finite front window. This only
proves return of the window; it says nothing about the white-witness test. -/
theorem universal_front_period (K a p : Nat) (ha : a < 2^(K+1)) (hp : p < 2) :
    orb (K+1) (2^(K+1)) (a,p) = (a,p) := by
  induction K generalizing a p with
  | zero =>
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
      rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;> decide +kernel
  | succ K ih =>
    let b := a % 2^(K+1)
    have hb : b < 2^(K+1) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hinit : LowEq (K+1) a b := by
      intro i hi
      simp only [b, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
    have hh := double_period (K := K+1) (a := a) (b := b) (p := p)
      (L := 2^(K+1)) ha hp hinit (ih b p hb hp)
    have hn : 2^(K+1)+2^(K+1) = 2^((K+1)+1) := by
      calc
        2^(K+1)+2^(K+1) = 2^(K+1)*2 := by omega
        _ = 2^((K+1)+1) := (Nat.pow_succ 2 (K+1)).symm
    simpa only [hn] using hh

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontPeriod
