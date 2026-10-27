module

public import Ruliology.CellularAutomata.Rule30Certificates.DrivenEmptyCore
public import Ruliology.CellularAutomata.Rule30EmptyGateSpacingResearch

/-!
# A stronger certified output language of the empty-right gate

At cycle 155 the driven right half enters a smaller finite wall. Its eight-bit
gate windows exclude two successive short gaps. This refines the earlier
three-or-five spacing theorem; it does not prove finite-support impossibility.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EmptyGateLanguageResearch

open Rule30DrivenPrefixResearch Rule30PeriodTwoSideways Rule30Certificates
open Rule30SpacingRenormalizationResearch

theorem core_trim (a : Nat) : DrivenEmptyCore.wall (a%2^18)=DrivenEmptyCore.wall a := by
  unfold DrivenEmptyCore.wall
  rw [Nat.mod_mod_of_dvd a (by decide : 65536 ∣ 2^18)]

theorem core_step (a : Nat) (ha : DrivenEmptyCore.wall a=true) :
    DrivenEmptyCore.Observe a ∧ DrivenEmptyCore.wall (double a)=true := by
  have ht : DrivenEmptyCore.wall (a%262144)=true := by
    change DrivenEmptyCore.wall (a%2^18)=true
    rw [core_trim]
    exact ha
  have hg := DrivenEmptyCore.good_all (a%262144) (Nat.mod_lt _ (by decide)) ht
  refine ⟨(DrivenEmptyCore.observe_trim a).mp hg.1,?_⟩
  have he : DrivenEmptyCore.wall (double (a%2^18))=DrivenEmptyCore.wall (double a) := by
    unfold DrivenEmptyCore.wall
    rw [← double_prefix a 16]
  rw [he] at hg
  exact hg.2

theorem white_core : ∀ n, DrivenEmptyCore.wall (white (155+n))=true
  | 0 => DrivenEmptyCore.entry
  | n+1 => by
      rw [show 155+(n+1)=(155+n)+1 by omega,white]
      exact (core_step _ (white_core n)).2

def refinedGate (r : Nat) : Bool := u empty (155+r)

theorem refinedGate_eq (r : Nat) :
    refinedGate r=Rule30EmptyGateSpacingResearch.gate (9+r) := by
  unfold refinedGate Rule30EmptyGateSpacingResearch.gate
  congr 1
  omega

theorem refined_spaced : Spaced refinedGate := by
  intro r
  have h := Rule30EmptyGateSpacingResearch.empty_spaced (9+r)
  simpa only [Nat.add_assoc,← refinedGate_eq] using h

theorem refined_next_gap (r : Nat) (hr : refinedGate r=true) :
    (refinedGate (r+3)=true ∧ refinedGate (r+4)=false ∧ refinedGate (r+5)=false) ∨
    (refinedGate (r+3)=false ∧ refinedGate (r+4)=false ∧ refinedGate (r+5)=true) := by
  have hr' := (refinedGate_eq r).symm.trans hr
  have h := Rule30EmptyGateSpacingResearch.empty_next_gap (9+r) hr'
  simpa only [Nat.add_assoc,← refinedGate_eq] using h

/-- In particular, a gap of three can never be followed by another gap of three. -/
theorem no_successive_short_gaps (r : Nat) :
    (refinedGate r && refinedGate (r+3) && refinedGate (r+6))=false := by
  have h := (core_step _ (white_core r)).1.1
  simpa only [iterate_white,white_gate,refinedGate,Nat.add_assoc,Nat.add_zero] using h

def windowWord (r : Nat) : Nat :=
  ((refinedGate r).toNat <<< 0) ||| ((refinedGate (r+1)).toNat <<< 1) |||
  ((refinedGate (r+2)).toNat <<< 2) ||| ((refinedGate (r+3)).toNat <<< 3) |||
  ((refinedGate (r+4)).toNat <<< 4) ||| ((refinedGate (r+5)).toNat <<< 5) |||
  ((refinedGate (r+6)).toNat <<< 6) ||| ((refinedGate (r+7)).toNat <<< 7)

theorem windowWord_allowed (r : Nat) :
    windowWord r ∈ [8,9,16,18,33,36,66,72,132,144] := by
  have h := (core_step _ (white_core r)).1.2
  simpa only [DrivenEmptyCore.word8,windowWord,iterate_white,white_gate,refinedGate,
    Nat.add_assoc,Nat.add_zero] using h

end Ruliology.CellularAutomata.Rule30EmptyGateLanguageResearch
