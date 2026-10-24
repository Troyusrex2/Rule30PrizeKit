import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! Width projection and certificate lifting for front-window searches.
These lemmas do not assert that arbitrary finite tails have certificates. -/

namespace Rule30FrontLiftResearch
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

def LowEq (n a b : Nat) : Prop := ∀ i, i < n → a.testBit i = b.testBit i

theorem parity_of_bit0 {a b : Nat} (h : a.testBit 0 = b.testBit 0) : a % 2 = b % 2 := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp_all [Nat.testBit_zero]

theorem pstep_low {n a b : Nat} (h : LowEq (n+1) a b) :
    LowEq n (pstepN a) (pstepN b) := by
  intro i hi
  change ((a >>> 1) ^^^ (a ||| (a <<< 1))).testBit i =
    ((b >>> 1) ^^^ (b ||| (b <<< 1))).testBit i
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  rw [h (1+i) (by omega), h i (by omega), h (i-1) (by omega)]

theorem sig_congr {n r s a b : Nat} (hp : r % 2 = s % 2) (h : LowEq n a b) :
    sig n r a = sig n s b := by
  induction n generalizing r s a b with
  | zero => rfl
  | succ n ih =>
    have hm := parity_of_bit0 (h 0 (by omega))
    have ht : (r+1) % 2 = (s+1) % 2 := by omega
    change Bool.rec (motive := fun _ => Bool) (sig n (r+1) (pstepN a)) true
      (band (Nat.beq (r%2) 0) (Nat.beq (a%2) 0)) =
        Bool.rec (motive := fun _ => Bool) (sig n (s+1) (pstepN b)) true
          (band (Nat.beq (s%2) 0) (Nat.beq (b%2) 0))
    rw [hp, hm, ih ht (pstep_low h)]

theorem sig_mono {n m r a : Nat} (hn : n ≤ m) (ha : sig n r a = true) :
    sig m r a = true := by
  induction n generalizing m r a with
  | zero => cases ha
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      change Bool.rec (sig n (r+1) (pstepN a)) true
        (band (Nat.beq (r%2) 0) (Nat.beq (a%2) 0)) = true at ha
      change Bool.rec (sig m (r+1) (pstepN a)) true
        (band (Nat.beq (r%2) 0) (Nat.beq (a%2) 0)) = true
      cases hc : band (Nat.beq (r%2) 0) (Nat.beq (a%2) 0) with
      | false =>
        have hh : sig n (r+1) (pstepN a) = true := by simpa only [hc] using ha
        exact ih (by omega) hh
      | true => rfl

theorem fstep_low {n K₁ K₂ a b p : Nat} (h₁ : n ≤ K₁) (h₂ : n ≤ K₂)
    (h : LowEq n a b) (hp : p < 2) :
    LowEq n (fstep K₁ a p) (fstep K₂ b p) := by
  intro i hi
  rw [testBit_fstep K₁ a p i hp, testBit_fstep K₂ b p i hp]
  simp only [show decide (i < K₁) = true from decide_eq_true (by omega),
    show decide (i < K₂) = true from decide_eq_true (by omega), Bool.true_and,
    h i hi, h (i-1) (by omega), h (i-2) (by omega)]

theorem orbit_low {n K₁ K₂ a b p : Nat} (h₁ : n ≤ K₁) (h₂ : n ≤ K₂)
    (h : LowEq n a b) (hp : p < 2) (t : Nat) :
    (orb K₁ t (a,p)).2 = (orb K₂ t (b,p)).2 ∧
      (orb K₁ t (a,p)).2 < 2 ∧
      LowEq n (orb K₁ t (a,p)).1 (orb K₂ t (b,p)).1 := by
  induction t with
  | zero => exact ⟨rfl, hp, h⟩
  | succ t ih =>
    rcases ih with ⟨he, hp', hlow⟩
    change (1-(orb K₁ t (a,p)).2 = 1-(orb K₂ t (b,p)).2) ∧
      1-(orb K₁ t (a,p)).2 < 2 ∧
      LowEq n (fstep K₁ (orb K₁ t (a,p)).1 (orb K₁ t (a,p)).2)
        (fstep K₂ (orb K₂ t (b,p)).1 (orb K₂ t (b,p)).2)
    refine ⟨by rw [he], by omega, ?_⟩
    rw [← he]
    exact fstep_low h₁ h₂ hlow hp'

/-- Reuse all successful residues of a smaller front cycle. A larger cycle
only needs separate witness checks on the lifted exceptional residues.
The higher-width period and the exceptional checks remain explicit premises. -/
theorem punctured_cycle_lift
    {Klo Khi Slo Shi A B p L H : Nat}
    (hK : Slo+1 ≤ Klo) (hwidth : Klo ≤ Khi) (hS : Slo ≤ Shi)
    (hp : p < 2) (hinit : LowEq Klo A B)
    (hL : 0 < L) (hLe : L % 2 = 0)
    (hLo : orb Klo L (B,p) = (B,p))
    (hH : 0 < H) (hHe : H % 2 = 0)
    (hHi : orb Khi H (A,p) = (A,p))
    (E : Nat → Prop)
    (hgood : ∀ r, r < L → r % 2 = 1-p → ¬ E r →
      sig (Slo+1) r (orb Klo r (B,p)).1 = true)
    (hrare : ∀ r, r < H → r % 2 = 1-p → E (r%L) →
      sig (Shi+1) r (orb Khi r (A,p)).1 = true) :
    Cycle Khi Shi A p H := by
  classical
  refine ⟨hHe, hH, hHi, ?_⟩
  intro r hr hpar
  simp only [Nat.zero_add] at hpar ⊢
  by_cases he : E (r%L)
  · exact hrare r hr hpar he
  · have hm : (r%L)%2 = r%2 :=
      Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hLe)
    have hs := hgood (r%L) (Nat.mod_lt _ hL) (by omega) he
    have ho := orb_mod Klo L (B,p) hLo r
    rw [← ho] at hs
    have hb := (orbit_low (n := Klo) (K₁ := Khi) (K₂ := Klo)
      (a := A) (b := B) (p := p) hwidth (Nat.le_refl _) hinit hp r).2.2
    have hl : LowEq (Slo+1) (orb Klo r (B,p)).1 (orb Khi r (A,p)).1 := by
      intro i hi
      exact (hb i (by omega)).symm
    have hc := sig_congr hm hl
    rw [hc] at hs
    exact sig_mono (by omega) hs

end Rule30FrontLiftResearch
