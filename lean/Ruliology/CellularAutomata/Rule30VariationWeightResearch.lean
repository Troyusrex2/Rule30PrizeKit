module

public import Ruliology.CellularAutomata.Rule30PackedReconstructionResearch

/-!
# An open variation/weight estimate sufficient for the period-two question

`VariationEstimate` is an OPEN hypothesis. Its implication to `Q01` uses
bounded variation and the kit's nonperiodicity theorem for the free bits of
a finitely supported constrained row. The strict factor-two candidate is
refuted by an exact finite cone; it is not used as an axiom or assumption.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30VariationWeightResearch

open Rule30Jen Rule30ZeroBoundary Rule30PackedReconstructionResearch

def variation (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => variation f n + if f n = f (n+1) then 0 else 1

def weight (L : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => weight L n + if L (n+1) then 1 else 0

theorem variation_mono (f : Nat → Bool) {n m : Nat} (h : n ≤ m) :
    variation f n ≤ variation f m := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      rw [show n+(d+1)=(n+d)+1 by omega,variation]
      split <;> omega

theorem weight_le (L : Nat → Bool) : ∀ n, weight L n ≤ n
  | 0 => by simp [weight]
  | n+1 => by
      rw [weight]
      have h := weight_le L n
      cases L (n+1) <;> simp_all <;> omega

theorem weight_fin (L : Nat → Bool) (W : Nat) (hW : ∀ k, W < k → L k = false) :
    ∀ n, weight L n ≤ W := by
  intro n
  induction n with
  | zero => simp [weight]
  | succ n ih =>
      by_cases hn : n+1 ≤ W
      · exact Nat.le_trans (weight_le L (n+1)) hn
      · rw [weight,hW (n+1) (by omega)]
        simpa using ih

theorem bounded_variation_periodic (f : Nat → Bool) (B : Nat)
    (hB : ∀ n, variation f n ≤ B) : EventuallyPeriodic f := by
  classical
  have key : ∀ B, (∀ n, variation f n ≤ B) →
      ∃ T, ∀ t, T ≤ t → f (t+1) = f t := by
    intro B
    induction B with
    | zero =>
        intro h
        refine ⟨0,fun t _ => ?_⟩
        have ht := h (t+1)
        by_cases he : f t = f (t+1)
        · exact he.symm
        · simp only [variation,he,ite_false] at ht
          omega
    | succ B ih =>
        intro h
        by_cases he : ∃ T, variation f T = B+1
        · obtain ⟨T,hT⟩ := he
          refine ⟨T,fun t ht => ?_⟩
          have hm := variation_mono f ht
          have hu := h (t+1)
          by_cases hf : f t = f (t+1)
          · exact hf.symm
          · simp only [variation,hf,ite_false] at hu
            omega
        · apply ih
          intro n
          have hn := h n
          have hne : variation f n ≠ B+1 := fun hn => he ⟨n,hn⟩
          omega
  obtain ⟨T,hT⟩ := key B hB
  exact ⟨T,1,by decide,hT⟩

/-- Open: one pair of constants works for every free sequence and every depth. -/
def VariationEstimate : Prop := ∃ C K : Nat, ∀ f : Nat → Bool, ∀ n,
  variation f n ≤ C * weight (Theta f) (2*n+3) + K

/-- The open estimate would settle `Q01`; the estimate itself is not proved. -/
theorem q01_of_variation_estimate (h : VariationEstimate) : Q01 := by
  obtain ⟨C,K,h⟩ := h
  rw [Q01_iff_Theta]
  intro f hfin
  obtain ⟨W,hW⟩ := hfin
  have hv : ∀ n, variation f n ≤ C*W+K := by
    intro n
    have h1 := h f n
    have h2 := Nat.mul_le_mul_left C (weight_fin (Theta f) W hW (2*n+3))
    omega
  obtain ⟨T,P,hP,hper⟩ := bounded_variation_periodic f _ hv
  apply free_not_eventuallyPeriodic ⟨W,hW⟩ (Theta_inX f)
  refine ⟨T,P,hP,fun t ht => ?_⟩
  change zrow (Theta f) (2*(t+P)+1) 1 = zrow (Theta f) (2*t+1) 1
  rw [Theta_free,Theta_free]
  exact hper t ht

/-- This conditional conclusion excludes period two, not every eventual period. -/
theorem no_period_two_of_variation_estimate (h : VariationEstimate) :
    ¬ ∃ T, ∀ t, T ≤ t → Rule30Prize.center (t+2) = Rule30Prize.center t :=
  no_eventual_period_two (q01_of_variation_estimate h)

theorem weight_congr (L M : Nat → Bool) : ∀ n,
    (∀ k, 1 ≤ k → k ≤ n → L k = M k) → weight L n = weight M n
  | 0,_ => rfl
  | n+1,h => by
      rw [weight,weight,weight_congr L M n (fun k h1 h2 => h k h1 (by omega)),
        h (n+1) (by omega) (by omega)]

def counterFree (n : Nat) : Bool := (726542922 : Nat).testBit n
def counterBoundary : Nat := 2152568877968356829
def counterInitial : Nat := 9147936877320643

theorem counter_variation : variation counterFree 29 = 21 := by decide

theorem counter_boundary_bits : ∀ t : Fin 62,
    counterBoundary.testBit t = alt counterFree t := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem counter_packed_cells : ∀ i : Fin 61,
    (packedRun counterBoundary (i.val+1)).1.testBit 0 = counterInitial.testBit i := by decide

set_option maxRecDepth 100000 in
theorem counter_weight : weight (Theta counterFree) 61 = 10 := by
  have hc : ∀ k, 1 ≤ k → k ≤ 61 → Theta counterFree k = counterInitial.testBit (k-1) := by
    intro k hk h61
    have h := (packed_sound counterBoundary 62 (alt counterFree)
      (fun t ht => counter_boundary_bits ⟨t,ht⟩) k 0 (by omega)).1
    have ht := counter_packed_cells ⟨k-1,by omega⟩
    rw [show k-1+1=k by omega] at ht
    change recon (alt counterFree) k 0 = _
    exact h.symm.trans ht
  rw [weight_congr (Theta counterFree) (fun k => counterInitial.testBit (k-1)) 61 hc]
  decide

/-- The factor-two estimate without an additive constant already fails at n=29. -/
theorem strict_factor_two_false :
    ¬ (∀ f : Nat → Bool, ∀ n,
      variation f n ≤ 2 * weight (Theta f) (2*n+3)) := by
  intro h
  have hc := h counterFree 29
  rw [show 2*29+3=61 from rfl,counter_variation,counter_weight] at hc
  omega

end Ruliology.CellularAutomata.Rule30VariationWeightResearch
