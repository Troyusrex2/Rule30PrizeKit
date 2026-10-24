import Ruliology.CellularAutomata.Rule30StripeMeeting
import Rule30AncestryResearch

/-! The lightweight ancestry module uses the adopted catalog's exact frame.
This bridge checks that identity and states its counterexample with catalog
constants. No trace-completeness or prize theorem is asserted. -/

namespace Rule30AncestryCatalogBridge

open Ruliology.CellularAutomata.Rule30StripeMeeting

theorem Phi_agrees (a : Nat) : Rule30AncestryResearch.Phi a = Phi a := rfl

theorem phiRows_agree (a t : Nat) :
    Rule30AncestryResearch.phiRows a t = phiRows a t := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [Rule30AncestryResearch.phiRows, phiRows, ih] using Phi_agrees (phiRows a t)

theorem prefix_agrees (a b c n : Nat) :
    Rule30AncestryResearch.SameCenterPrefix a b c n ↔ SameCenterPrefix a b c n := by
  simp only [Rule30AncestryResearch.SameCenterPrefix, SameCenterPrefix, phiRows_agree]

theorem official_short_ancestry_horizon_counterexample :
    ∃ a b n c : Nat, 0 < a ∧ 0 < b ∧ a < 2^n ∧ b < 2^n ∧ c < n ∧
      SameCenterPrefix a b c (2*n+2) ∧
      (∃ x : Nat, Phi x = a) ∧ ¬ (∃ x : Nat, Phi x = b) := by
  obtain ⟨a,b,n,c,ha,hb,han,hbn,hc,hprefix,hparent,hnoparent⟩ :=
    Rule30AncestryResearch.short_ancestry_horizon_counterexample
  exact ⟨a,b,n,c,ha,hb,han,hbn,hc,(prefix_agrees a b c _).mp hprefix,
    hparent,hnoparent⟩

end Rule30AncestryCatalogBridge
