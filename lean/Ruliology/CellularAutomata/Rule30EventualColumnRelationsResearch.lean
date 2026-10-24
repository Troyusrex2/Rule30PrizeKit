module

public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# Two eventual spatial relations excluded by monotonicity

In every orbit with a leftmost black cell, columns distance two apart cannot
eventually agree, and adjacent columns cannot eventually be complements.
The first relation makes the middle column monotone; the second makes the
left column monotone. Neither result excludes a temporal period of one column,
nor does it establish eventual separation for arbitrary spatial distances.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EventualColumnRelationsResearch

open Rule30Jen Rule30Realization

theorem middle_step {x : Int → Bool} {i : Int} {t : Nat}
    (h : evol x t (i+2) = evol x t i) :
    evol x (t+1) (i+1) = (evol x t (i+1) && !evol x t i) := by
  change rule (evol x t (i+1-1)) (evol x t (i+1)) (evol x t (i+1+1)) = _
  rw [show i+1-1=i by omega, show i+1+1=i+2 by omega,h]
  cases evol x t i <;> cases evol x t (i+1) <;> rfl

/-- This statement needs no hypothesis on the starting configuration. -/
theorem middle_eventually_constant {x : Int → Bool} {i : Int} {T : Nat}
    (h : ∀ t, T ≤ t → evol x t (i+2) = evol x t i) :
    ∃ S b, ∀ t, S ≤ t → evol x t (i+1) = b := by
  have hm : ∀ t, T ≤ t → (!evol x t (i+1)) = true →
      (!evol x (t+1) (i+1)) = true := by
    intro t ht he
    rw [middle_step (h t ht)]
    have hf : evol x t (i+1) = false := by
      cases hc : evol x t (i+1) <;> simp_all
    rw [hf]
    rfl
  obtain ⟨S,b,hb⟩ := Rule30Prize.eventually_const_of_mono
    (f := fun t => !evol x t (i+1)) hm
  refine ⟨S,!b,fun t ht => ?_⟩
  have he := hb t ht
  cases hbv : b <;> cases hcv : evol x t (i+1) <;> simp_all

/-- Infinitely many disagreements, uniformly for all configurations with a leftmost black cell. -/
theorem distance_two_infinitely_different {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hz : ∀ p, p < lo → x p = false) (i : Int) (T : Nat) :
    ∃ t, T ≤ t ∧ evol x t (i+2) ≠ evol x t i := by
  classical
  apply Classical.byContradiction
  intro hn
  have he : ∀ t, T ≤ t → evol x t (i+2) = evol x t i := by
    intro t ht
    exact Classical.byContradiction (fun hne => hn ⟨t,ht,hne⟩)
  exact Rule30FiniteConfigs.no_column_eventually_constant hlo hz (i+1)
    (middle_eventually_constant he)

theorem adjacent_complement_monotone {x : Int → Bool} {i : Int} {T : Nat}
    (h : ∀ t, T ≤ t → evol x t (i+1) = !evol x t i) :
    ∀ t, T ≤ t → (!evol x t i) = true → (!evol x (t+1) i) = true := by
  intro t ht he
  have hn := h (t+1) (by omega)
  change rule (evol x t (i+1-1)) (evol x t (i+1)) (evol x t (i+1+1)) =
    !evol x (t+1) i at hn
  rw [show i+1-1=i by omega,h t ht] at hn
  have hf : evol x t i = false := by
    cases hc : evol x t i <;> simp_all
  rw [hf] at hn
  simpa [rule] using hn.symm

theorem adjacent_not_complement {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hz : ∀ p, p < lo → x p = false) (i : Int) (T : Nat) :
    ∃ t, T ≤ t ∧ evol x t (i+1) ≠ !evol x t i := by
  classical
  apply Classical.byContradiction
  intro hn
  have he : ∀ t, T ≤ t → evol x t (i+1) = !evol x t i := by
    intro t ht
    exact Classical.byContradiction (fun hne => hn ⟨t,ht,hne⟩)
  obtain ⟨S,b,hb⟩ := Rule30Prize.eventually_const_of_mono
    (f := fun t => !evol x t i) (adjacent_complement_monotone he)
  apply Rule30FiniteConfigs.no_column_eventually_constant hlo hz i
  refine ⟨S,!b,fun t ht => ?_⟩
  have e := hb t ht
  cases hbv : b <;> cases hcv : evol x t i <;> simp_all

end Ruliology.CellularAutomata.Rule30EventualColumnRelationsResearch
