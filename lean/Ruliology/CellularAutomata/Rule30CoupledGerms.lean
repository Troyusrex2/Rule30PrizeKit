module

public import Ruliology.CellularAutomata.Rule30Coupled

/-!
# Recurring RIGHT germs in coupled Rule 30 histories

For the driven RIGHT half, define `gamma(t)` as cell1 AND(cell2 ORcell3).
Suppose that from time T the driver avoids11 and gamma is zero at every fall.
After a black driver cell at some S >= T, the complete nearest-RIGHT trace from
S+2 onward equals the complemented one-tick-delayed driver. This transport uses
neither periodicity, finite support nor LEFT compatibility.

For an eventually periodic driver with arbitrarily late black cells and eventually
no11, literal coupling and Jen rigidity force gamma to be ONE at arbitrarily late
falls whenever the LEFT has a finite positive edge, or both coupled halves are
finite (including an initially empty LEFT).

The method is a two-tick Boolean identity followed by induction on the driver.
The periodicity and contradiction steps reuse the catalog's LEFT reconstruction,
coupling/gluing and driven-LEFT or finite-configuration Jen theorems.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30CoupledGerms

open Ruliology.CellularAutomata
open Rule30Jen Rule30Realization Rule30DrivenLeft Rule30Ether Rule30Coupled

/-- The same three actual RIGHT cells, in the official driven model. -/
def drivenGamma (omega x : Nat → Bool) (t : Nat) : Bool :=
  drv omega x t 1 && (drv omega x t 2 || drv omega x t 3)

/-- No adjacent ONE pair after a specified actual time. -/
def EventuallyNo11 (omega : Nat → Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → (omega t && omega (t + 1)) = false

/-- The germ is zero at every sufficiently late black-to-white driver transition. -/
def EventuallyZeroGamma (omega x : Nat → Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → omega t = true → omega (t + 1) = false →
    drivenGamma omega x t = false

/-- ONE occurs arbitrarily late; preperiod-only ONEs do not suffice. -/
def CofinalBlack (omega : Nat → Bool) : Prop :=
  ∀ N, ∃ t, N ≤ t ∧ omega t = true

/-- Established two-tick germ identity, only transported to the official `drv` model. -/
theorem driven_right_two (omega x : Nat → Bool) (S : Nat)
    (hc : omega S = true) (hn : omega (S + 1) = false) :
    drv omega x (S + 2) 1 = !drivenGamma omega x S := by
  change rule (drv omega x (S + 1) 0) (drv omega x (S + 1) 1)
    (drv omega x (S + 1) 2) = _
  rw [drv_col0, hn]
  simp only [rule, Bool.false_xor]
  change (rule (drv omega x S 0) (drv omega x S 1) (drv omega x S 2) ||
    rule (drv omega x S 1) (drv omega x S 2) (drv omega x S 3)) = _
  rw [drv_col0, hc]
  unfold drivenGamma
  cases drv omega x S 1 <;> cases drv omega x S 2 <;> cases drv omega x S 3 <;> rfl

theorem driven_right_step (omega x : Nat → Bool) (t : Nat) :
    drv omega x (t + 1) 1 = xor (omega t)
      (drv omega x t 1 || drv omega x t 2) := by
  change rule (drv omega x t 0) (drv omega x t 1) (drv omega x t 2) = _
  rw [drv_col0]
  rfl

/-- Complete general transport. Periodicity, finite support and LEFT compatibility
are not used: an all-falls zero germ fixes the late RIGHT root one tick behind
the center. This is an exact equality, not a finite-prefix observation. -/
theorem right_root_gamma_transport (omega x : Nat → Bool) (T S : Nat)
    (hS : T ≤ S) (hblack : omega S = true)
    (hno11 : ∀ t, T ≤ t → (omega t && omega (t + 1)) = false)
    (hgamma : ∀ t, T ≤ t → omega t = true → omega (t + 1) = false →
      drivenGamma omega x t = false) :
    ∀ n, drv omega x (S + 2 + n) 1 = !omega (S + 1 + n) := by
  have hn : omega (S + 1) = false := by
    have he := hno11 S hS
    simpa [hblack] using he
  intro n
  induction n with
  | zero =>
    simp only [Nat.add_zero]
    rw [driven_right_two omega x S hblack hn, hgamma S hS hblack hn, hn]
  | succ n ih =>
    have hindex : S + 1 + (n + 1) = S + 2 + n := by omega
    rw [hindex]
    cases hnow : omega (S + 2 + n) with
    | false =>
      cases hprev : omega (S + 1 + n) with
      | false =>
        have hr : drv omega x (S + 2 + n) 1 = true := by simpa [hprev] using ih
        rw [show S + 2 + (n + 1) = (S + 2 + n) + 1 by omega,
          driven_right_step, hnow, hr]
        rfl
      | true =>
        have hn' : omega ((S + 1 + n) + 1) = false := by
          simpa [show S + 1 + n + 1 = S + 2 + n by omega] using hnow
        have he := driven_right_two omega x (S + 1 + n) hprev hn'
        rw [hgamma (S + 1 + n) (by omega) hprev hn'] at he
        simpa [show S + 1 + n + 2 = S + 2 + (n + 1) by omega] using he
    | true =>
      have hprev : omega (S + 1 + n) = false := by
        have he := hno11 (S + 1 + n) (by omega)
        rw [show S + 1 + n + 1 = S + 2 + n by omega, hnow] at he
        simpa using he
      have hr : drv omega x (S + 2 + n) 1 = true := by simpa [hprev] using ih
      rw [show S + 2 + (n + 1) = (S + 2 + n) + 1 by omega,
        driven_right_step, hnow, hr]
      rfl

/-- Periodicity enters only here, after the full transport equality. -/
theorem right_root_periodic_of_zero_gamma (omega x : Nat → Bool)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hgamma : EventuallyZeroGamma omega x) (hblack : CofinalBlack omega) :
    EventuallyPeriodic (fun t => drv omega x t 1) := by
  obtain ⟨Tp, P, hP, hp⟩ := hper
  obtain ⟨Tn, hn⟩ := hno11
  obtain ⟨Tg, hg⟩ := hgamma
  let T := max Tn Tg
  obtain ⟨S, hS, hb⟩ := hblack T
  have htr := right_root_gamma_transport omega x T S hS hb
    (fun t ht => hn t (by omega)) (fun t ht => hg t (by omega))
  refine ⟨max (S + 2) (Tp + 1), P, hP, ?_⟩
  intro t ht
  have he := htr (t - (S + 2))
  have hep := htr (t + P - (S + 2))
  have hi : S + 2 + (t - (S + 2)) = t := by omega
  have hip : S + 2 + (t + P - (S + 2)) = t + P := by omega
  rw [hi] at he
  rw [hip] at hep
  change drv omega x (t + P) 1 = drv omega x t 1
  rw [hep, he]
  have hi' : S + 1 + (t - (S + 2)) = t - 1 := by omega
  have hip' : S + 1 + (t + P - (S + 2)) = (t - 1) + P := by omega
  rw [hi', hip', hp (t - 1) (by omega)]

/-- Both full driven roots are compatible with the same column. Their periods
combine through the exact coupled center equation. -/
theorem coupled_left_periodic_of_right (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    (hper : EventuallyPeriodic omega)
    (hr : EventuallyPeriodic (fun t => drv omega x t 1)) :
    EventuallyPeriodic (fun t => L omega s t (-1)) := by
  obtain ⟨T, P, hP, hp, hq⟩ := common_period hper hr
  refine ⟨T, P, hP, ?_⟩
  intro t ht
  have he := hc (t + P)
  have hf := hc t
  rw [show t + P + 1 = (t + 1) + P by omega, hp (t + 1) (by omega),
    hp t ht, hq t ht] at he
  unfold rule at he hf
  cases L omega s (t + P) (-1) <;> cases L omega s t (-1) <;>
    cases omega t <;> cases drv omega x t 1 <;> simp_all

/-- Exact Coupled-model consumer. No boundary-placeholder compatibility assumptions
are needed: `Coupled` already uses the official center `omega` at depth zero. -/
theorem coupled_left_periodic_of_zero_gamma (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hgamma : EventuallyZeroGamma omega x) (hblack : CofinalBlack omega) :
    EventuallyPeriodic (fun t => L omega s t (-1)) :=
  coupled_left_periodic_of_right omega s x hc hper
    (right_root_periodic_of_zero_gamma omega x hper hno11 hgamma hblack)

/-- A finite nonzero LEFT source with its true occupied edge cannot satisfy
the additional all-late-falls zero-gamma hypothesis. RIGHT finiteness is unused. -/
theorem coupled_zero_gamma_impossible_of_left_edge (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    {m : Nat} (hm : 0 < m)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hgamma : EventuallyZeroGamma omega x) (hblack : CofinalBlack omega) : False :=
  col_neg_one_not_periodic hs0 hs1 hm hper
    (coupled_left_periodic_of_zero_gamma omega s x hc hper hno11 hgamma hblack)

/-- Actual finite-configuration version. The center is definitionally the same
initial center `y 0`; no placeholder value is substituted. -/
theorem finite_config_zero_gamma_impossible (y : Int → Bool)
    (hfin : Rule30PeriodTwoSideways.FinConfig y) (hne : ∃ p, y p = true)
    (hper : EventuallyPeriodic (fun t => evol y t 0))
    (hno11 : EventuallyNo11 (fun t => evol y t 0))
    (hgamma : EventuallyZeroGamma (fun t => evol y t 0) (fun p => y (p : Int)))
    (hblack : CofinalBlack (fun t => evol y t 0)) : False := by
  have hp := coupled_left_periodic_of_zero_gamma
    (fun t => evol y t 0) y (fun p => y (p : Int)) (coupled_of_evol y)
    hper hno11 hgamma hblack
  have hl : EventuallyPeriodic (fun t => evol y t (-1)) := by
    obtain ⟨T, P, hP, hp'⟩ := hp
    refine ⟨T, P, hP, ?_⟩
    intro t ht
    change evol y (t + P) (-1) = evol y t (-1)
    rw [left_eq_L y (t + P) (-1) (by omega), left_eq_L y t (-1) (by omega)]
    exact hp' t ht
  exact Rule30FiniteConfigs.jen_finite hfin hne (-1) 0 (by decide) ⟨hl, hper⟩

/-- Full official CQ-model version: finite halves, both coupled to the SAME
column, cannot have gamma zero at all late falls in the covered domain.
The glued full row uses `omega 0` regardless of `s 0` or `x 0`. -/
theorem coupled_finite_zero_gamma_impossible (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    (hleft : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false)
    (hright : ∃ W : Nat, ∀ p, W < p → x p = false)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hgamma : EventuallyZeroGamma omega x) (hblack : CofinalBlack omega) : False := by
  let y := glue s (omega 0) x
  have hfin : Rule30PeriodTwoSideways.FinConfig y := by
    obtain ⟨Wl, hl⟩ := hleft
    obtain ⟨Wr, hr⟩ := hright
    refine ⟨Wl + Wr, ?_⟩
    intro p hp
    dsimp only [y, glue]
    by_cases hn : p < 0
    · rw [ite_eq_left hn]
      exact hl p (by omega)
    · rw [ite_eq_right hn, ite_eq_right (by omega)]
      exact hr _ (by omega)
  have hne : ∃ p, y p = true := by
    refine Classical.byContradiction fun h => ?_
    have hz : ∀ p, y p = false := by
      intro p
      cases he : y p with
      | false => rfl
      | true => exact False.elim (h ⟨p, he⟩)
    obtain ⟨t, _, ht⟩ := hblack 0
    have he := Rule30Coupled.evol_zero hz t 0
    change evol (glue s (omega 0) x) t 0 = false at he
    rw [center_glue hc] at he
    rw [ht] at he
    contradiction
  have hcp : EventuallyPeriodic (fun t => evol y t 0) := by
    obtain ⟨T, P, hP, hp⟩ := hper
    refine ⟨T, P, hP, ?_⟩
    intro t ht
    change evol (glue s (omega 0) x) (t + P) 0 =
      evol (glue s (omega 0) x) t 0
    rw [center_glue hc, center_glue hc]
    exact hp t ht
  have hlp := coupled_left_periodic_of_zero_gamma omega s x hc hper hno11 hgamma hblack
  have hl : EventuallyPeriodic (fun t => evol y t (-1)) := by
    obtain ⟨T, P, hP, hp⟩ := hlp
    refine ⟨T, P, hP, ?_⟩
    intro t ht
    change evol (glue s (omega 0) x) (t + P) (-1) =
      evol (glue s (omega 0) x) t (-1)
    rw [evol_glue hc, evol_glue hc]
    simpa using hp t ht
  exact Rule30FiniteConfigs.jen_finite hfin hne (-1) 0 (by decide) ⟨hl, hcp⟩

/-- Exact Boolean duality, retaining both fall letters. -/
theorem cofinal_gamma_of_not_eventually_zero (omega x : Nat → Bool)
    (h : ¬ EventuallyZeroGamma omega x) :
    ∀ N, ∃ t, N ≤ t ∧ omega t = true ∧ omega (t + 1) = false ∧
      drivenGamma omega x t = true := by
  intro N
  refine Classical.byContradiction fun hn => ?_
  apply h
  refine ⟨N, ?_⟩
  intro t ht hb hf
  cases he : drivenGamma omega x t with
  | false => rfl
  | true => exact False.elim (hn ⟨t, ht, hb, hf, he⟩)

/-- The recurring-germ statement with only a finite positive LEFT edge.
No finite RIGHT assumption or all-gamma-zero premise remains. -/
theorem coupled_gamma_cofinal_of_left_edge (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    {m : Nat} (hm : 0 < m)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hblack : CofinalBlack omega) :
    ∀ N, ∃ t, N ≤ t ∧ omega t = true ∧ omega (t + 1) = false ∧
      drivenGamma omega x t = true := by
  apply cofinal_gamma_of_not_eventually_zero
  intro hg
  exact coupled_zero_gamma_impossible_of_left_edge omega s x hc hm hs0 hs1
    hper hno11 hg hblack

/-- Recurring gamma for the full official CQ finite-halves model, including
initially empty LEFT halves. Both boundary placeholders remain irrelevant. -/
theorem coupled_finite_gamma_cofinal (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    (hleft : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false)
    (hright : ∃ W : Nat, ∀ p, W < p → x p = false)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hblack : CofinalBlack omega) :
    ∀ N, ∃ t, N ≤ t ∧ omega t = true ∧ omega (t + 1) = false ∧
      drivenGamma omega x t = true := by
  apply cofinal_gamma_of_not_eventually_zero
  intro hg
  exact coupled_finite_zero_gamma_impossible omega s x hc hleft hright
    hper hno11 hg hblack

end Ruliology.CellularAutomata.Rule30CoupledGerms
