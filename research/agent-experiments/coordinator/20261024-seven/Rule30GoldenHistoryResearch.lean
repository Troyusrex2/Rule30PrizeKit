import Rule30GoldenEvenWidth20Research

namespace Rule30GoldenHistoryResearch
open Ruliology.CellularAutomata
open Rule30Prize
open Rule30ZeroBoundary (alt recon zrow)
open Rule30GoldenDFAResearch (Golden)
open Rule30GoldenEvenSupportResearch (code NoGoldenEvenWidth)

theorem history_code {L : Nat → Bool} {s : Nat → Bool}
    (h : ∀ t, zrow L t 1 = alt s t) (d : Nat) : code s d = L (2*d+2) := by
  have ha : (fun t => zrow L t 1) = alt s := funext h
  have hc := Rule30ZeroBoundary.history_eq_recon L (2*d+2) 0
  rw [ha] at hc
  exact hc.symm

/-- Even support alone suffices; the odd spatial coordinates are arbitrary. -/
theorem not_golden_history {M : Nat} (hM : NoGoldenEvenWidth M)
    {L : Nat → Bool} {s : Nat → Bool}
    (hh : ∀ t, zrow L t 1 = alt s t)
    (he : ∀ d, M ≤ d → L (2*d+2) = false) : ¬ Golden s := by
  apply hM s
  intro d hd
  rw [history_code hh d]
  exact he d hd

theorem not_golden_history_even_width20 {L : Nat → Bool} {s : Nat → Bool}
    (hh : ∀ t, zrow L t 1 = alt s t)
    (he : ∀ d, 20 ≤ d → L (2*d+2) = false) : ¬ Golden s :=
  not_golden_history Rule30GoldenEvenWidth20Research.noGoldenEvenWidth20 hh he

def free (T k : Nat) : Bool := Rule30Jen.cell (T+2*k+1) (-1)

theorem golden_free {T : Nat}
    (hT : ∀ k, Rule30Jen.cell (T+2*k) 0 = true ∧ Rule30Jen.cell (T+2*k+1) 0 = false) :
    Golden (free T) := by
  constructor
  · intro k hk
    cases hb : free T (k+1)
    · exact False.elim ((Rule30ZeroBoundary.free_bits_no00_no11111 hT k).1 ⟨hk,hb⟩)
    · rfl
  · intro k ⟨h0,h1,h2,h3,h4⟩
    apply (Rule30ZeroBoundary.free_bits_no00_no11111 hT k).2
    intro i hi
    rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 by omega) with rfl | rfl | rfl | rfl | rfl
    · simpa only [free,Nat.add_zero] using h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4

theorem history_eq_alt_free {T : Nat}
    (hT : ∀ k, Rule30Jen.cell (T+2*k) 0 = true ∧ Rule30Jen.cell (T+2*k+1) 0 = false) :
    ∀ t, zrow (Rule30ZeroBoundary.leftRow T) t 1 = alt (free T) t := by
  have hw : ∀ t, T ≤ t → (center t && center (t+1)) = false := by
    intro t ht
    obtain ⟨k,hk | hk⟩ : ∃ k, t = T+2*k ∨ t = T+2*k+1 := ⟨(t-T)/2,by omega⟩
    · subst t
      change (Rule30Jen.cell (T+2*k) 0 && Rule30Jen.cell (T+2*k+1) 0) = false
      rw [(hT k).2]
      cases Rule30Jen.cell (T+2*k) 0 <;> rfl
    · subst t
      change (Rule30Jen.cell (T+2*k+1) 0 && center (T+2*k+1+1)) = false
      rw [(hT k).2]
      rfl
  intro t
  rw [Rule30ZeroBoundary.left_half_is_zbl hw t 1 (by omega)]
  obtain ⟨k,rfl | rfl⟩ : ∃ k, t=2*k ∨ t=2*k+1 := ⟨t/2,by omega⟩
  · rw [Rule30GoldenEvenSupportResearch.alt_even]
    exact Rule30PeriodTwo.m1_even hT k
  · rw [Rule30GoldenEvenSupportResearch.alt_odd]
    rfl

theorem not_alternating_of_even_width {M T : Nat} (hM : NoGoldenEvenWidth M)
    (he : ∀ d, M ≤ d → Rule30ZeroBoundary.leftRow T (2*d+2) = false) :
    ¬ ∀ k, Rule30Jen.cell (T+2*k) 0 = true ∧ Rule30Jen.cell (T+2*k+1) 0 = false := by
  intro hT
  exact not_golden_history hM (history_eq_alt_free hT) he (golden_free hT)

theorem not_alternating_of_even_width20 (T : Nat)
    (he : ∀ d, 20 ≤ d → Rule30ZeroBoundary.leftRow T (2*d+2) = false) :
    ¬ ∀ k, Rule30Jen.cell (T+2*k) 0 = true ∧ Rule30Jen.cell (T+2*k+1) 0 = false :=
  not_alternating_of_even_width Rule30GoldenEvenWidth20Research.noGoldenEvenWidth20 he

end Rule30GoldenHistoryResearch
