import Ruliology.CellularAutomata.Rule30StripeMeeting
import Ruliology.CellularAutomata.Rule30ZeroBoundarySmall
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! Elementary nonlinear conjugacy identities for the actual integer update.
No unbounded group-growth or trace-separation claim is made. -/

namespace Rule30GroupPrimitivesResearch
open Ruliology.CellularAutomata
open Rule30StripeMeeting

def g0 (a : Nat) : Nat := a ^^^ 2^0
def g1 (a : Nat) : Nat := a ^^^ (if a.testBit 0 = a.testBit 1 then 7 else 3)
def h (a : Nat) : Nat := g0 (g1 a)

theorem g0_involution (a : Nat) : g0 (g0 a) = a := by
  simp [g0, Nat.xor_assoc]

theorem g1_bit0 (a : Nat) : (g1 a).testBit 0 = !(a.testBit 0) := by
  cases h0 : a.testBit 0 <;> cases h1 : a.testBit 1 <;>
    simp only [g1, Nat.testBit_xor, h0, h1] <;> decide +kernel

theorem g1_bit1 (a : Nat) : (g1 a).testBit 1 = !(a.testBit 1) := by
  cases h0 : a.testBit 0 <;> cases h1 : a.testBit 1 <;>
    simp only [g1, Nat.testBit_xor, h0, h1] <;> decide +kernel

theorem g1_high (a i : Nat) (hi : 3 ≤ i) : (g1 a).testBit i = a.testBit i := by
  have h7 : (7:Nat).testBit i = false :=
    Rule30ZeroBoundarySmall.testBit_ge_of_lt (W := 3) (by decide) hi
  have h3 : (3:Nat).testBit i = false :=
    Rule30ZeroBoundarySmall.testBit_ge_of_lt (W := 3) (by decide) hi
  unfold g1
  split <;> rw [Nat.testBit_xor] <;> simp only [h7, h3, Bool.xor_false]

theorem g1_involution (a : Nat) : g1 (g1 a) = a := by
  have he : ((g1 a).testBit 0 = (g1 a).testBit 1) ↔ (a.testBit 0 = a.testBit 1) := by
    rw [g1_bit0, g1_bit1]
    cases a.testBit 0 <;> cases a.testBit 1 <;> decide
  change g1 a ^^^ (if (g1 a).testBit 0 = (g1 a).testBit 1 then 7 else 3) = a
  simp only [he]
  simp only [g1, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem phi_flip_high (a i : Nat) (hi : 3 ≤ i) :
    (Phi (g0 a)).testBit i = (Phi a).testBit i := by
  simp only [Phi, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft,
    g0, Nat.testBit_two_pow]
  simp [show 0 ≠ i by omega, show 0 ≠ i-1 by omega, show 0 ≠ i-2 by omega]

/-- On the image of Phi, g1 is Phi composed with the low-bit flip and Phi's
inverse. Its explicit finite-prefix extension is an involution on all Nats. -/
theorem phi_intertwines_flip (a : Nat) : Phi (g0 a) = g1 (Phi a) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | hi
  · cases h0 : a.testBit 0 <;> cases h1 : a.testBit 1 <;>
      simp only [Phi_testBit, before, g0, g1, Nat.testBit_xor, h0, h1] <;> decide +kernel
  · cases h0 : a.testBit 0 <;> cases h1 : a.testBit 1 <;>
      simp only [Phi_testBit, before, g0, g1, Nat.testBit_xor, h0, h1] <;> decide +kernel
  · cases h0 : a.testBit 0 <;> cases h1 : a.testBit 1 <;> cases h2 : a.testBit 2 <;>
      simp only [Phi_testBit, before, g0, g1, Nat.testBit_xor, h0, h1, h2] <;> decide +kernel
  · rw [phi_flip_high a i hi, g1_high (Phi a) i hi]

theorem h_square (a : Nat) : h (h a) = a ^^^ 4 := by
  cases h0 : a.testBit 0 <;> cases h1 : a.testBit 1 <;>
    simp only [h, g0, g1, Nat.testBit_xor, h0, h1, Nat.xor_assoc] <;> dsimp <;> rfl

theorem h_fourth (a : Nat) : h (h (h (h a))) = a := by
  rw [h_square, h_square]
  simp [Nat.xor_assoc]

theorem flips_do_not_commute : g0 (g1 0) ≠ g1 (g0 0) := by decide +kernel

def Phi90 (a : Nat) : Nat := a ^^^ (a <<< 2)
def g90 (a : Nat) : Nat := a ^^^ 5

theorem phi90_intertwines_flip (a : Nat) : Phi90 (g0 a) = g90 (Phi90 a) := by
  unfold Phi90 g0 g90
  rw [Nat.shiftLeft_xor_distrib]
  change (a ^^^ 1) ^^^ ((a <<< 2) ^^^ 4) = (a ^^^ (a <<< 2)) ^^^ 5
  simp only [Nat.xor_assoc]
  rw [← Nat.xor_assoc 1 (a <<< 2) 4, Nat.xor_comm 1 (a <<< 2), Nat.xor_assoc (a <<< 2) 1 4]
  rfl

theorem linear_flips_commute (a : Nat) : g0 (g90 a) = g90 (g0 a) := by
  simp only [g0, g90, Nat.xor_assoc]
  rfl

open Rule30ZeroBoundaryStripeFront

theorem short_period_return32 : orb 6 32 (1,0) = (1,0) := by decide +kernel

theorem short_period_no_return :
    (List.range 31).all (fun t => decide (orb 6 (t+1) (1,0) ≠ (1,0))) = true := by
  decide +kernel

theorem short_period_minimal (t : Nat) (ht : 0 < t) (hb : t < 32) :
    orb 6 t (1,0) ≠ (1,0) := by
  have h := List.all_eq_true.mp short_period_no_return (t-1) (List.mem_range.mpr (by omega))
  have he : t-1+1 = t := by omega
  rw [he] at h
  exact of_decide_eq_true h

end Rule30GroupPrimitivesResearch
