module

public import Ruliology.CellularAutomata.Rule30BlackRuns

@[expose] public section

namespace PhysicalEarlyCases

open Ruliology.CellularAutomata
open Rule30Jen Rule30BlackRuns

/-- A stationary row survives on the ordinary shrinking radius-one cone. -/
theorem stationary_cone (f : Int → Bool)
    (hf : ∀ p, rule (f (p - 1)) (f p) (f (p + 1)) = f p)
    (a : Nat) (L U : Int)
    (hrow : ∀ p, L ≤ p → p ≤ U → cell a p = f p) :
    ∀ s : Nat, ∀ p : Int, L + s ≤ p → p + s ≤ U → cell (a + s) p = f p
  | 0, p, hlo, hhi => by simpa using hrow p (by omega) (by omega)
  | s + 1, p, hlo, hhi => by
    show rule (cell (a + s) (p - 1)) (cell (a + s) p)
      (cell (a + s) (p + 1)) = f p
    rw [stationary_cone f hf a L U hrow s (p - 1) (by omega) (by omega),
      stationary_cone f hf a L U hrow s p (by omega) (by omega),
      stationary_cone f hf a L U hrow s (p + 1) (by omega) (by omega)]
    exact hf p

/-- Odd columns black and even columns white form a stationary Rule 30 row. -/
def stripe (p : Int) : Bool := decide (p % 2 = 1)

theorem stripe_stationary (p : Int) :
    rule (stripe (p - 1)) (stripe p) (stripe (p + 1)) = stripe p := by
  by_cases hp : p % 2 = 0
  · have hl : (p - 1) % 2 = 1 := by omega
    have hr : (p + 1) % 2 = 1 := by omega
    simp [stripe, hp, hl, hr, rule]
  · have hp1 : p % 2 = 1 := by omega
    have hl : (p - 1) % 2 = 0 := by omega
    have hr : (p + 1) % 2 = 0 := by omega
    simp [stripe, hp1, hl, hr, rule]

/-- The white boundary protects a shrinking initially white positive prefix. -/
theorem white_prefix (a K : Nat) (M : Int)
    (hc : ∀ r, r < K → cell (a + r) 0 = false)
    (hrow : ∀ p : Int, 1 ≤ p → p ≤ M → cell a p = false) :
    ∀ s : Nat, s ≤ K → ∀ p : Int, 1 ≤ p → p + s ≤ M →
      cell (a + s) p = false
  | 0, _, p, hlo, hhi => by simpa using hrow p hlo (by omega)
  | s + 1, hs, p, hlo, hhi => by
    show rule (cell (a + s) (p - 1)) (cell (a + s) p)
      (cell (a + s) (p + 1)) = false
    have hl : cell (a + s) (p - 1) = false := by
      by_cases hp : p = 1
      · rw [show p - 1 = 0 by omega]
        exact hc s (by omega)
      · exact white_prefix a K M hc hrow s (by omega) (p - 1) (by omega) (by omega)
    rw [hl, white_prefix a K M hc hrow s (by omega) p hlo (by omega),
      white_prefix a K M hc hrow s (by omega) (p + 1) (by omega) (by omega)]
    rfl

/-- A black column 1 followed by 9n white center ticks gives a protected white witness. -/
theorem early_white_witness_at (n a j : Nat) (hn : 1 ≤ n) (hj : j < n)
    (hc : ∀ r, r < 9 * n → cell (a + r) 0 = false)
    (hb : cell a 1 = true) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ 2 * n + 1 ∧ cell (a + 9 * n + j) p = false := by
  have hblack : ∀ r, r ≤ 9 * n → cell (a + r) 1 = true :=
    black_stays a (9 * n) hc hb
  have hshield := black_shield 1 n a (fun r hr => hblack r (by omega))
  have hrow : ∀ p : Int, 1 ≤ p → p ≤ 2 * (n : Int) + 1 →
      cell (a + 9 * n) p = stripe p := by
    intro p hlo hhi
    have hcast : (p.toNat : Int) = p := by omega
    by_cases hp : p % 2 = 0
    · let i := p.toNat / 2
      have hi1 : 1 ≤ i := by dsimp [i]; omega
      have hin : i ≤ n := by dsimp [i]; omega
      have heq : (1 : Int) + 2 * (i : Int) - 1 = p := by dsimp [i]; omega
      have hs := (hshield i hi1 hin).1
      rw [heq] at hs
      simpa [stripe, hp] using hs
    · have hp1 : p % 2 = 1 := by omega
      by_cases hone : p = 1
      · subst p
        simpa [stripe] using hblack (9 * n) (Nat.le_refl _)
      · let i := p.toNat / 2
        have hi1 : 1 ≤ i := by dsimp [i]; omega
        have hin : i ≤ n := by dsimp [i]; omega
        have heq : (1 : Int) + 2 * (i : Int) = p := by dsimp [i]; omega
        have hs := (hshield i hi1 hin).2
        rw [heq] at hs
        simpa [stripe, hp1] using hs
  let p := n + n % 2
  have hp1 : 1 ≤ p := by dsimp [p]; omega
  have hp2 : p ≤ 2 * n + 1 := by dsimp [p]; omega
  have heven : (p : Int) % 2 = 0 := by dsimp [p]; omega
  refine ⟨p, hp1, hp2, ?_⟩
  have hs := stationary_cone stripe stripe_stationary (a + 9 * n) 1
    (2 * (n : Int) + 1) hrow j p (by dsimp [p]; omega) (by dsimp [p]; omega)
  simpa [stripe, heven] using hs

theorem early_white_witness (n N t j : Nat) (hn : 1 ≤ n) (hj : j < n)
    (hwhite : ∀ r, r < N + 9 * n → cell (t + r) 0 = false)
    (hblack : cell (t + N) 1 = true) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ 2 * n + 1 ∧ cell (t + (N + 9 * n) + j) p = false := by
  have hc : ∀ r, r < 9 * n → cell (t + N + r) 0 = false := by
    intro r hr
    have h := hwhite (N + r) (by omega)
    simpa [Nat.add_assoc] using h
  simpa [Nat.add_assoc] using early_white_witness_at n (t + N) j hn hj hc hblack

/-- A distant all-white prefix leaves p=n white after the warmup and j<n arbitrary ticks. -/
theorem distant_white_witness_at (n a j : Nat) (hn : 1 ≤ n) (hj : j < n)
    (hc : ∀ r, r < 9 * n → cell (a + r) 0 = false)
    (hprefix : ∀ p : Int, 1 ≤ p → p < 11 * (n : Int) → cell a p = false) :
    cell (a + 9 * n + j) n = false := by
  have hrow : ∀ p : Int, 1 ≤ p → p ≤ 2 * (n : Int) - 1 →
      cell (a + 9 * n) p = false := by
    intro p hlo hhi
    exact white_prefix a (9 * n) (11 * (n : Int) - 1) hc
      (fun q hq1 hq2 => hprefix q hq1 (by omega)) (9 * n) (Nat.le_refl _) p hlo (by omega)
  exact stationary_cone (fun _ => false) (fun _ => rfl) (a + 9 * n)
    1 (2 * (n : Int) - 1) hrow j n (by omega) (by omega)

theorem distant_white_witness (n N t j : Nat) (hn : 1 ≤ n) (hj : j < n)
    (hwhite : ∀ r, r < 9 * n → cell (t + N + r) 0 = false)
    (hprefix : ∀ p : Int, 1 ≤ p → p < 11 * (n : Int) → cell (t + N) p = false) :
    cell (t + (N + 9 * n) + j) n = false := by
  simpa [Nat.add_assoc] using distant_white_witness_at n (t + N) j hn hj hwhite hprefix

end PhysicalEarlyCases
