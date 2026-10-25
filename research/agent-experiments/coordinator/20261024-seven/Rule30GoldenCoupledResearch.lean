import Rule30GoldenHistoryResearch
import Rule30VerifiedCoupledGoldenExtract

/-! A conditional uniform route and a checked finite-even-support consequence.
The golden-language input comes from Villafuerte/Antigravity's independently
replayed verified submission, not a new claim of this module. -/

namespace Rule30GoldenCoupledResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary (alt zrow FinSupp)
open Rule30PeriodTwoSideways (Psi)
open Rule30GoldenDFAResearch (Golden)
open Rule30GoldenEvenSupportResearch (NoGoldenEvenWidth)

def free (R : Nat → Bool) (k : Nat) : Bool := zrow (Psi R) (2*k+1) 1

theorem golden_free (R : Nat → Bool) : Golden (free R) := by
  constructor
  · intro k hk
    cases hb : free R (k+1)
    · exact False.elim ((Rule30Submission.Psi_free_no00_no11111 R k).1 ⟨hk,hb⟩)
    · rfl
  · intro k ⟨h0,h1,h2,h3,h4⟩
    apply (Rule30Submission.Psi_free_no00_no11111 R k).2
    intro i hi
    rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 by omega) with rfl | rfl | rfl | rfl | rfl
    · simpa only [free,Nat.add_zero] using h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4

theorem history_eq_alt (R : Nat → Bool) : ∀ t, zrow (Psi R) t 1 = alt (free R) t := by
  intro t
  obtain ⟨k,rfl | rfl⟩ : ∃ k, t=2*k ∨ t=2*k+1 := ⟨t/2,by omega⟩
  · rw [Rule30GoldenEvenSupportResearch.alt_even]
    exact Rule30PeriodTwoSideways.Psi_inX R k
  · rw [Rule30GoldenEvenSupportResearch.alt_odd]
    rfl

/-- For arbitrary right halves, including infinite ones, a certificate at
width M forces a black even coordinate of the sideways row beyond M. -/
theorem psi_even_escape {M : Nat} (hM : NoGoldenEvenWidth M) (R : Nat → Bool) :
    ∃ d, M ≤ d ∧ Psi R (2*d+2) = true := by
  classical
  apply Classical.byContradiction
  intro hn
  have he : ∀ d, M ≤ d → Psi R (2*d+2) = false := by
    intro d hd
    cases hb : Psi R (2*d+2)
    · rfl
    · exact False.elim (hn ⟨d,hd,hb⟩)
  exact Rule30GoldenHistoryResearch.not_golden_history hM (history_eq_alt R) he (golden_free R)

theorem psi_even_escape20 (R : Nat → Bool) : ∃ d, 20 ≤ d ∧ Psi R (2*d+2) = true :=
  psi_even_escape Rule30GoldenEvenWidth20Research.noGoldenEvenWidth20 R

/-- This is a reduction, not a proof of the unproved uniform premise. -/
theorem not_finSupp_psi_of_uniform (hu : ∀ M, NoGoldenEvenWidth M) (R : Nat → Bool) :
    ¬ FinSupp (Psi R) := by
  rintro ⟨W,hW⟩
  obtain ⟨d,hd,hb⟩ := psi_even_escape (hu W) R
  rw [hW (2*d+2) (by omega)] at hb
  cases hb

theorem CQ01_of_uniform (hu : ∀ M, NoGoldenEvenWidth M) : Rule30PeriodTwoCoupled.CQ01 := by
  apply Rule30PeriodTwoSideways.CQ01_iff_Psi.mpr
  intro R _
  exact not_finSupp_psi_of_uniform hu R

end Rule30GoldenCoupledResearch
