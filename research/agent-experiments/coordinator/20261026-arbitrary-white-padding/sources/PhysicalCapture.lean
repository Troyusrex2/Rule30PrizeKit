module

public import PhysicalEarlyCases

@[expose] public section

namespace PhysicalCapture

open Ruliology.CellularAutomata
open Rule30Jen Rule30BlackRuns

/- Generic nearest-cell/white-run arguments extracted from the hash-pinned
public source. The literal-width black_step is generalized to arbitrary B.
Only the official kit and the independently frozen EarlyCases are imported. -/

/-! ### B. The jump law on actual cells -/

theorem cell_succ (t : Nat) (p : Int) :
    cell (t + 1) p = rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) := rfl

/-- Some column among `1 … m` is black at time `t`. -/
def Near (t m : Nat) : Prop := ∃ p : Nat, 1 ≤ p ∧ p ≤ m ∧ cell t p = true

theorem near_min {t : Nat} : ∀ m, Near t m →
    ∃ p : Nat, 1 ≤ p ∧ p ≤ m ∧ cell t p = true ∧ ∀ q : Nat, 1 ≤ q → q < p → cell t q = false
  | 0, ⟨p, hp1, hp0, _⟩ => by omega
  | m + 1, ⟨p, hp1, hpm, hb⟩ => by
    rcases Classical.em (Near t m) with hn | hn
    · obtain ⟨p', h1, h2, h3, h4⟩ := near_min m hn
      exact ⟨p', h1, Nat.le_succ_of_le h2, h3, h4⟩
    · refine ⟨p, hp1, hpm, hb, fun q hq1 hq2 => ?_⟩
      cases hc : cell t q with
      | false => rfl
      | true => exact (hn ⟨q, hq1, by omega, hc⟩).elim

/-- White tick, first black cell at column `p ≥ 3`: it moves to column `p - 1`. -/
theorem white_step_far (t p : Nat) (h0 : cell t 0 = false) (hp : 3 ≤ p)
    (hw : ∀ q : Nat, 1 ≤ q → q < p → cell t q = false) (hb : cell t p = true) :
    cell (t + 1) ((p - 1 : Nat) : Int) = true := by
  rw [cell_succ]
  have e1 : ((p - 1 : Nat) : Int) - 1 = ((p - 2 : Nat) : Int) := by omega
  have e2 : ((p - 1 : Nat) : Int) + 1 = (p : Int) := by omega
  rw [e1, e2, hw (p-2) (by omega) (by omega), hw (p-1) (by omega) (by omega), hb]
  rfl

/-- White tick with a black cell in columns `1, 2`: column `1` is black next. -/
theorem white_step_near (t : Nat) (h0 : cell t 0 = false) (h : cell t 1 = true ∨ cell t 2 = true) :
    cell (t + 1) 1 = true := by
  rw [cell_succ]
  have e : (1 : Int) - 1 = 0 := by omega
  rw [e, h0]
  rcases h with h | h
  · rw [h]; rfl
  · rw [show (1 : Int) + 1 = 2 by omega, h]; cases cell t 1 <;> rfl

theorem near_white_step {t m : Nat} (h0 : cell t 0 = false) (hm : 2 ≤ m) (h : Near t m) :
    Near (t + 1) (m - 1) := by
  obtain ⟨p, hp1, hpm, hb, hmin⟩ := near_min m h
  by_cases hp3 : 3 ≤ p
  · refine ⟨p - 1, by omega, by omega, ?_⟩
    exact white_step_far t p h0 hp3 hmin hb
  · refine ⟨1, Nat.le_refl 1, by omega, white_step_near t h0 ?_⟩
    have hp : p = 1 ∨ p = 2 := by omega
    rcases hp with rfl | rfl
    · exact Or.inl hb
    · exact Or.inr hb

theorem near_white_run {t m : Nat} :
    ∀ n, n + 1 ≤ m → (∀ s, s < n → cell (t + s) 0 = false) → Near t m → Near (t + n) (m - n) := by
  intro n
  induction n with
  | zero => intro _ _ h; simpa using h
  | succ n ih =>
    intro hn hw h
    have h1 := ih (by omega) (fun s hs => hw s (by omega)) h
    have h2 := near_white_step (m := m - n) (hw n (by omega)) (by omega) h1
    rw [show t + (n + 1) = t + n + 1 by omega, show m - (n + 1) = m - n - 1 by omega]
    exact h2

theorem white_min {t : Nat} : ∀ m, (∃ p : Nat, 1 ≤ p ∧ p ≤ m ∧ cell t p = false) →
    ∃ p : Nat, 1 ≤ p ∧ p ≤ m ∧ cell t p = false ∧ ∀ q : Nat, 1 ≤ q → q < p → cell t q = true
  | 0, ⟨p, hp1, hp0, _⟩ => by omega
  | m + 1, ⟨p, hp1, hpm, hb⟩ => by
    rcases Classical.em (∃ p : Nat, 1 ≤ p ∧ p ≤ m ∧ cell t p = false) with hn | hn
    · obtain ⟨p', h1, h2, h3, h4⟩ := white_min m hn
      exact ⟨p', h1, Nat.le_succ_of_le h2, h3, h4⟩
    · refine ⟨p, hp1, hpm, hb, fun q hq1 hq2 => ?_⟩
      cases hc : cell t q with
      | true => rfl
      | false => exact (hn ⟨q, hq1, by omega, hc⟩).elim

/-- Black tick, columns `1 … B` not all black: the next row has a black cell within `(B + 1)`. -/
theorem black_step (t B : Nat) (h0 : cell t 0 = true)
    (h : ∃ p : Nat, 1 ≤ p ∧ p ≤ B ∧ cell t p = false) : Near (t + 1) (B + 1) := by
  obtain ⟨p, hp1, hp14, hpw, hmin⟩ := white_min B h
  have hleft : cell t ((p : Int) - 1) = true := by
    by_cases hp1' : p = 1
    · subst hp1'; simpa using h0
    · have : ((p : Int) - 1) = ((p - 1 : Nat) : Int) := by omega
      rw [this]; exact hmin (p - 1) (by omega) (by omega)
  have hstep : cell (t + 1) p = !cell t ((p : Int) + 1) := by
    rw [cell_succ, hleft, hpw]; cases cell t ((p : Int) + 1) <;> rfl
  cases hc : cell t ((p : Int) + 1) with
  | false => exact ⟨p, hp1, by omega, by rw [hstep, hc]; rfl⟩
  | true =>
    refine ⟨p + 1, by omega, by omega, ?_⟩
    rw [cell_succ, show ((p + 1 : Nat) : Int) - 1 = (p : Int) by omega,
      show ((p + 1 : Nat) : Int) = (p : Int) + 1 by omega, hpw, hc]
    cases cell t ((p : Int) + 1 + 1) <;> rfl

/-- A nearby black cell after a black tick reaches column 1 and remains black
through the closed endpoint of the following white center run. -/
theorem capture_after_black (t B L : Nat) (h0 : cell t 0 = true)
    (hwitness : ∃ p : Nat, 1 ≤ p ∧ p ≤ B ∧ cell t p = false)
    (hw : ∀ s, s < L → cell (t + 1 + s) 0 = false) (hBL : B ≤ L) :
    ∀ s, B ≤ s → s ≤ L → cell (t + 1 + s) 1 = true := by
  have hnear := black_step t B h0 hwitness
  have harr := near_white_run (t := t + 1) (m := B + 1) B (by omega)
    (fun s hs => hw s (by omega)) hnear
  obtain ⟨p, hp1, hpB, hp⟩ := harr
  have heq : p = 1 := by omega
  subst p
  have hblack : cell (t + 1 + B) 1 = true := hp
  have htail := black_stays (t + 1 + B) (L - B) (fun r hr => by
    have h := hw (B + r) (by omega)
    simpa [Nat.add_assoc] using h) hblack
  intro s hs hsL
  have h := htail (s - B) (by omega)
  rwa [show t + 1 + B + (s - B) = t + 1 + s by omega] at h

/-- The shield plus its black column-1 endpoint is the complete fixed stripe. -/
theorem stripe_after_black_run (a K : Nat)
    (hb : ∀ r, r < 9 * K → cell (a + r) 1 = true)
    (hend : cell (a + 9 * K) 1 = true) :
    ∀ p : Int, 1 ≤ p → p ≤ 2 * (K : Int) + 1 →
      cell (a + 9 * K) p = PhysicalEarlyCases.stripe p := by
  have hshield := black_shield 1 K a hb
  intro p hlo hhi
  have hcast : (p.toNat : Int) = p := by omega
  by_cases hp : p % 2 = 0
  · let i := p.toNat / 2
    have hi1 : 1 ≤ i := by dsimp [i]; omega
    have hin : i ≤ K := by dsimp [i]; omega
    have heq : (1 : Int) + 2 * (i : Int) - 1 = p := by dsimp [i]; omega
    have hs := (hshield i hi1 hin).1
    rw [heq] at hs
    simpa [PhysicalEarlyCases.stripe, hp] using hs
  · have hp1 : p % 2 = 1 := by omega
    by_cases hone : p = 1
    · subst p
      simpa [PhysicalEarlyCases.stripe] using hend
    · let i := p.toNat / 2
      have hi1 : 1 ≤ i := by dsimp [i]; omega
      have hin : i ≤ K := by dsimp [i]; omega
      have heq : (1 : Int) + 2 * (i : Int) = p := by dsimp [i]; omega
      have hs := (hshield i hi1 hin).2
      rw [heq] at hs
      simpa [PhysicalEarlyCases.stripe, hp1] using hs

/-- A long enough white tail both captures a black column 1 and regenerates
the same complete alternating prefix at the endpoint. -/
theorem tail_and_stripe (t B K L : Nat) (h0 : cell t 0 = true)
    (hwitness : ∃ p : Nat, 1 ≤ p ∧ p ≤ B ∧ cell t p = false)
    (hw : ∀ s, s < L → cell (t + 1 + s) 0 = false)
    (hL : B + 9 * K ≤ L) :
    (∀ s, B ≤ s → s ≤ L → cell (t + 1 + s) 1 = true) ∧
    (∀ p : Int, 1 ≤ p → p ≤ 2 * (K : Int) + 1 →
      cell (t + 1 + L) p = PhysicalEarlyCases.stripe p) := by
  have htail := capture_after_black t B L h0 hwitness hw (by omega)
  refine ⟨htail, ?_⟩
  have hstripe := stripe_after_black_run (t + 1 + (L - 9 * K)) K (fun r hr => by
    have h := htail (L - 9 * K + r) (by omega) (by omega)
    simpa [Nat.add_assoc] using h) (by
    rw [show t + 1 + (L - 9 * K) + 9 * K = t + 1 + L by omega]
    exact htail L (by omega) (Nat.le_refl _))
  rwa [show t + 1 + (L - 9 * K) + 9 * K = t + 1 + L by omega] at hstripe

end PhysicalCapture
