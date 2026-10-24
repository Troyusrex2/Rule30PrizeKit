import Rule30PrizeKit
import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! The exact sensitivity one entry behind the reconstruction's newest
pivot. This does not prove a finite-support obstruction or a prize claim. -/

namespace Rule30OddSensitivityResearch

open Ruliology.CellularAutomata Rule30ZeroBoundary

def shoulder (a : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | k+1, t => xor (shoulder a k (t+1)) (!recon a (k+1) t)

/-- XOR of the anti-diagonal from depth k at time t to depth1 at time t+k-1. -/
def diagParity (a : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | k+1, t => xor (recon a (k+1) t) (diagParity a k (t+1))

theorem difference_step : ∀ a a' b b' c : Bool,
    xor (xor a (b || c)) (xor a' (b' || c)) =
      xor (xor a a') ((xor b b') && !c) := by decide +kernel

theorem factor_xor : ∀ x a b : Bool,
    xor (x && a) (x && b) = (x && xor a b) := by decide +kernel

/-- Change only the penultimate relevant head entry, keeping the newest
entry fixed. Its influence is controlled by the preceding anti-diagonal. -/
theorem recon_shoulder_difference (k : Nat) : ∀ (a b : Nat → Bool) (t : Nat),
    (∀ j, j < k → a (t+j) = b (t+j)) → a (t+k+1) = b (t+k+1) →
    xor (recon a (k+2) t) (recon b (k+2) t) =
      ((xor (a (t+k)) (b (t+k))) && shoulder a k t) := by
  induction k with
  | zero =>
      intro a b t _ hn
      simp only [Nat.add_zero] at hn ⊢
      simp only [recon, Bool.or_false, hn, shoulder, Bool.and_true]
      cases a t <;> cases b t <;> cases b (t+1) <;> rfl
  | succ k ih =>
      intro a b t hp hn
      have hc := recon_local (a := a) (b := b) (k+1) t hp
      have hv := recon_aff (k+1) a b t hp
      have hi := ih a b (t+1) (fun j hj => by
        have := hp (j+1) (by omega)
        simpa only [show t+(j+1) = t+1+j by omega] using this)
        (by simpa only [show t+1+k+1 = t+(k+1)+1 by omega] using hn)
      rw [show t+1+k = t+(k+1) by omega] at hi
      change xor
        (xor (recon a (k+2) (t+1)) (recon a (k+2) t || recon a (k+1) t))
        (xor (recon b (k+2) (t+1)) (recon b (k+2) t || recon b (k+1) t)) = _
      rw [← hc, difference_step, hi, hv, factor_xor]
      rfl

theorem shoulder_parity (a : Nat → Bool) (k t : Nat) :
    shoulder a k t = xor (decide (k % 2 = 0)) (diagParity a k t) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
      have hc : decide ((k+1) % 2 = 0) = !decide (k % 2 = 0) := by
        by_cases h : k % 2 = 0
        · have hn : (k+1) % 2 ≠ 0 := by omega
          simp [h, hn]
        · have hn : (k+1) % 2 = 0 := by omega
          simp [h, hn]
      rw [shoulder, ih, diagParity, hc]
      cases decide (k%2=0) <;> cases diagParity a k (t+1) <;>
        cases recon a (k+1) t <;> rfl

def flipAt (a : Nat → Bool) (n i : Nat) : Bool := xor (a i) (decide (i=n))

theorem recon_flipAt (a : Nat → Bool) (k t : Nat) :
    xor (recon a (k+2) t) (recon (flipAt a (t+k)) (k+2) t) = shoulder a k t := by
  have h := recon_shoulder_difference k a (flipAt a (t+k)) t
    (fun j hj => by simp [flipAt, show j ≠ k by omega])
    (by simp [flipAt])
  have hx : xor (a (t+k)) (flipAt a (t+k) (t+k)) = true := by
    simp only [flipAt, decide_true, Bool.xor_true]
    cases a (t+k) <;> rfl
  simpa only [hx, Bool.true_and] using h

theorem alt_flipAt (s : Nat → Bool) (d : Nat) :
    alt (flipAt s d) = flipAt (alt s) (2*d+1) := by
  funext i
  by_cases h : i % 2 = 0
  · have hn : i ≠ 2*d+1 := by omega
    simp [alt, flipAt, h, hn]
  · have he : (i/2=d) ↔ i=2*d+1 := by omega
    simp only [alt, h, ite_false, flipAt, he]

/-- Unlike even spatial cells, the next odd spatial cell need not have a
unit free-bit pivot. Its exact pivot is an anti-diagonal parity. -/
theorem odd_free_flip (s : Nat → Bool) (d : Nat) :
    xor (Theta s (2*d+3)) (Theta (flipAt s d) (2*d+3)) =
      diagParity (alt s) (2*d+1) 0 := by
  change xor (recon (alt s) (2*d+3) 0) (recon (alt (flipAt s d)) (2*d+3) 0) = _
  rw [alt_flipAt]
  have h := recon_flipAt (alt s) (2*d+1) 0
  rw [shoulder_parity] at h
  have hpar : decide ((2*d+1)%2=0) = false := decide_eq_false (by omega)
  simpa only [Nat.zero_add, show 2*d+1+2 = 2*d+3 by omega,
    hpar, Bool.false_xor] using h

end Rule30OddSensitivityResearch
