module

public import Ruliology.CellularAutomata.Rule30EmptyGateSpacingResearch

/-!
# The remaining finite-support step, with the physical time shift explicit

The reconstructed row for the certified gate is exactly the original sideways
row evolved for 293 steps. Finite support propagates forwards. No converse
finite-preimage assertion is made. `CostEstimate` is OPEN; its implication
below is a research target, not a proof of `CQ01Empty`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EmptyGateReductionResearch

open Rule30ZeroBoundary Rule30PeriodTwoSideways
open Rule30EmptyGateSpacingResearch Rule30SpacingRenormalizationResearch

theorem shifted_history (t : Nat) :
    zrow (Psi empty) (t+293) 1=boundary gate t := by
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht
  · obtain ⟨r,hr⟩ : ∃ r, t=2*r := ⟨t/2,by omega⟩
    subst t
    rw [show 2*r+293=2*(146+r)+1 by omega,Psi_free]
    change (!u empty (146+r))=boundary gate (2*r)
    rw [boundary_even]
    rfl
  · obtain ⟨r,hr⟩ : ∃ r, t=2*r+1 := ⟨t/2,by omega⟩
    subst t
    rw [show 2*r+1+293=2*(147+r) by omega,(Psi_inX empty (147+r)),boundary_odd]

def shifted : Nat → Bool := lam (boundary gate)

/-- An unconditional equality with the actual sideways row, at every depth. -/
theorem shifted_eq (k : Nat) : shifted k=zrow (Psi empty) 293 k := by
  have hh : (fun t => zrow (Psi empty) (t+293) 1)=boundary gate :=
    funext shifted_history
  have hr := recon_shift (fun t => zrow (Psi empty) t 1) 293 k 0
  rw [hh] at hr
  have he := history_eq_recon (Psi empty) k 293
  exact hr.symm.trans he.symm

theorem finite_shifted_of_finite (h : FinSupp (Psi empty)) : FinSupp shifted := by
  obtain ⟨W,hW⟩ := h
  refine ⟨W+293,fun k hk => ?_⟩
  rw [shifted_eq]
  exact zrow_fin hW 293 k hk

/-- This is only a sufficient condition; no backward finite-support inference is used. -/
theorem CQ01Empty_of_not_finite_shifted (h : ¬ FinSupp shifted) : CQ01Empty :=
  fun hf => h (finite_shifted_of_finite hf)

def charge (L : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => charge L n + if L (n+1) then n+1 else 0

theorem charge_mono (L : Nat → Bool) {n m : Nat} (h : n≤m) : charge L n≤charge L m := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      rw [show n+(d+1)=(n+d)+1 by omega,charge]
      split <;> omega

theorem charge_fin (L : Nat → Bool) (W : Nat) (hW : ∀ k, W<k → L k=false) :
    ∀ n, charge L n≤charge L W
  | 0 => by simp [charge]
  | n+1 => by
      by_cases hn : n+1≤W
      · exact charge_mono L hn
      · rw [charge,hW (n+1) (by omega)]
        simpa using charge_fin L W hW n

/-- OPEN: this estimate is a target for synthesis, not an established premise. -/
def CostEstimate : Prop := ∃ C K : Nat, ∀ n, n≤C*charge shifted n+K

theorem not_finite_of_cost_estimate (h : CostEstimate) : ¬ FinSupp shifted := by
  obtain ⟨C,K,h⟩ := h
  rintro ⟨W,hW⟩
  have hn := h (C*charge shifted W+K+1)
  have hb := Nat.mul_le_mul_left C (charge_fin shifted W hW (C*charge shifted W+K+1))
  omega

/-- Conditional only: the open estimate itself is not proved here. -/
theorem CQ01Empty_of_cost_estimate (h : CostEstimate) : CQ01Empty :=
  CQ01Empty_of_not_finite_shifted (not_finite_of_cost_estimate h)

end Ruliology.CellularAutomata.Rule30EmptyGateReductionResearch
