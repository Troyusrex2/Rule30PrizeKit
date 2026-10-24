module

public import Ruliology.CellularAutomata.Rule30PairedTraceResearch
public import Ruliology.CellularAutomata.Rule30CenterRuns

/-!
# Quantitative obstruction for a hypothetical global ranking

Uses Luis Perez Morales and Claude's independently replayed PR 8 recurrence
theorems. Every dyadic center window contains both colors, hence at least one
flip. This gives explicit logarithmic growth forced on ANY `FlipRanking` along
the five-versus-three-cell family. No ranking is constructed, and no prize
problem or new period is excluded.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30QuantitativeRankResearch

open Rule30Jen Rule30Prize Rule30Realization Rule30ZeroBoundaryBarriers
open Rule30PairedTraceResearch

theorem flipCount_mono (f : Nat → Bool) {a b : Nat} (hab : a≤b) :
    flipCount f a≤flipCount f b := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      rw [show a+(d+1)=(a+d)+1 by omega,flipCount]
      split <;> omega

theorem flipCount_strict_of_ne (f : Nat → Bool) {a b : Nat} (hab : a≤b)
    (hne : f a≠f b) : flipCount f a<flipCount f b := by
  induction b generalizing a with
  | zero =>
      have ha : a=0 := by omega
      subst a
      exact False.elim (hne rfl)
  | succ b ih =>
      by_cases ha : a≤b
      · by_cases hv : f a=f b
        · have hf : f b≠f (b+1) := fun he => hne (hv.trans he)
          have hm := flipCount_mono f ha
          rw [flipCount,ite_eq_right hf]
          omega
        · have hi := ih ha hv
          have hm := flipCount_mono f (show b≤b+1 by omega)
          omega
      · have he : a=b+1 := by omega
        subst a
        exact False.elim (hne rfl)

theorem innerThree_seed_step : evol seed 1=innerThree := by
  funext p
  by_cases hm : p= -1
  · subst p; decide
  by_cases hz : p=0
  · subst p; decide
  by_cases hp : p=1
  · subst p; decide
  simp [evol,seed,rule,innerThree,hm,hz,hp,
    show p-1≠0 by omega,show p+1≠0 by omega]

theorem innerThree_trace (t : Nat) : evol innerThree t 0=center (t+1) := by
  rw [← innerThree_seed_step,evol_restart,evol_seed]
  change cell (1+t) 0=cell (t+1) 0
  rw [Nat.add_comm]

/-- Each dyadic interval of the shifted seed trace contains a color change. -/
theorem innerThree_flip_window (a : Nat) (ha : 1≤a) :
    flipCount (fun t => evol innerThree t 0) (a-1)<
      flipCount (fun t => evol innerThree t 0) (2*a-1) := by
  let f := fun t => evol innerThree t 0
  have ht (t : Nat) (h : 1≤t) : f (t-1)=center t := by
    dsimp [f]
    rw [innerThree_trace,show t-1+1=t by omega]
  have hex : ∃ t, a≤t ∧ t≤2*a ∧ center a≠center t := by
    cases hc : center a with
    | false =>
        obtain ⟨t,h1,h2,h3⟩ := Rule30CenterRuns.exists_black' a ha
        exact ⟨t,h1,by omega,by rw [h3]; decide⟩
    | true =>
        obtain ⟨t,h1,h2,h3⟩ := Rule30CenterRuns.exists_white a ha
        exact ⟨t,h1,h2,by rw [h3]; decide⟩
  obtain ⟨t,h1,h2,h3⟩ := hex
  have hn : f (a-1)≠f (t-1) := by rw [ht a ha,ht t (by omega)]; exact h3
  have hs := flipCount_strict_of_ne f (show a-1≤t-1 by omega) hn
  have hm := flipCount_mono f (show t-1≤2*a-1 by omega)
  exact Nat.lt_of_lt_of_le hs hm

theorem innerThree_dyadic_flips : ∀ m,
    m≤flipCount (fun t => evol innerThree t 0) (2^m-1)
  | 0 => Nat.zero_le _
  | m+1 => by
      have hs := innerThree_flip_window (2^m) Nat.one_le_two_pow
      have hi := innerThree_dyadic_flips m
      rw [Nat.pow_succ]
      have he : 2^m*2=2*2^m := Nat.mul_comm _ _
      rw [he]
      omega

/-- At outer radius `2^m+2`, a hypothetical ranking already needs value `m`.
Both rows still have only five and three initial black cells. -/
theorem sparse_rank_dyadic_lower_bound
    (V : (Int → Bool) → (Int → Bool) → Nat) (hV : FlipRanking V) (m : Nat) :
    m≤V (outerFive (2^m+2)) innerThree := by
  have hc := sparse_flip_charge_bound V hV (2^m-1) (2^m-1) (Nat.le_refl _)
  have hi := innerThree_dyadic_flips m
  have hp : 1≤2^m := Nat.one_le_two_pow
  rw [show 2^m-1+3=2^m+2 by omega] at hc
  omega

end Ruliology.CellularAutomata.Rule30QuantitativeRankResearch
