module
public import FiniteHiddenPair
public import BlockHiddenPair
public import RightOneLayer
@[expose] public section
namespace HiddenPairRightObstruction
open Ruliology.CellularAutomata Rule30Jen Rule30DrivenLeft Rule30DrivenMaskTransport
open PeriodicHiddenPair (driver)

/-- The actual Rule 30 recurrence on every integer position, with no boundary clamp. -/
def FullHistory (X : Nat → Int → Bool) : Prop :=
  ∀ t p, X (t+1) p=rule (X t (p-1)) (X t p) (X t (p+1))

theorem official_history : FullHistory cell := by intro t p; rfl

theorem full_history_compatible {X : Nat → Int → Bool} (hX : FullHistory X) :
    RightOneLayer.Compatible (fun t=>X t 0) (fun t=>X t (-1)) := by
  refine ⟨(fun t=>X t 1),?_,?_⟩
  · intro t
    exact hX t 0
  · intro t ht
    change X t 1=true at ht
    change X (t+1) 1= !X t 0
    have h:=hX t 1
    change X (t+1) 1=rule (X t 0) (X t 1) (X t 2) at h
    rw [ht] at h
    cases hc : X t 0 <;> simpa [rule,hc] using h

theorem zero_rule_neighbors (l r : Bool) (h : false=rule l false r) : l=r := by
  cases l <;> cases r <;> first | rfl | cases h

/-- Elementary white-run persistence, expressed on the LEFT neighbor by two center
updates. This adapts the existing black-stays observation; it is not a new prize result. -/
theorem three_white_left_black_stays {X : Nat → Int → Bool} (hX : FullHistory X)
    (t : Nat) (p : Int) (h0 : X t p=false) (h1 : X (t+1) p=false)
    (h2 : X (t+2) p=false) (hl : X t (p-1)=true) : X (t+1) (p-1)=true := by
  have e0:=hX t p
  rw [h0,h1] at e0
  have equal0:=zero_rule_neighbors _ _ e0
  have hr : X t (p+1)=true := by rw [←equal0]; exact hl
  have er:=hX t (p+1)
  rw [show p+1-1=p by omega,h0,hr] at er
  have hr1 : X (t+1) (p+1)=true := by simpa [rule] using er
  have e1:=hX (t+1) p
  rw [show t+1+1=t+2 by omega,h1,h2] at e1
  have equal1:=zero_rule_neighbors _ _ e1
  rw [equal1]
  exact hr1

/-- The fixed-period hidden pair's false branch has NO full-space extension,
even with infinite starts on both sides. The contradiction uses times 2..4. -/
theorem periodic_false_branch_no_extension :
    ¬∃ X : Nat → Int → Bool, FullHistory X ∧ (∀ t,X t 0=driver t) ∧
      (∀ t,X t (-1)=PeriodicHiddenPair.profile false t 1) := by
  rintro ⟨X,hX,hc,hl⟩
  have h:=three_white_left_black_stays hX 2 0
    (by rw [hc];rfl) (by rw [hc];rfl) (by rw [hc];rfl)
    (by change X 2 (-1)=true;rw [hl];rfl)
  change X 3 (-1)=true at h
  rw [hl] at h
  change false=true at h
  cases h

theorem block_left_four (q : Nat → Bool) : BlockHiddenPair.profile q true 4 1=true := by
  change ((BlockHiddenPair.words (q 0) true)[4]?.getD 0).testBit 0=true
  cases q 0 <;> rfl
theorem block_left_five (q : Nat → Bool) : BlockHiddenPair.profile q true 5 1=false := by
  change ((BlockHiddenPair.words (q 0) true)[5]?.getD 0).testBit 0=false
  cases q 0 <;> rfl

theorem periodic_profile_not_compatible :
    ¬RightOneLayer.Compatible driver (fun t=>PeriodicHiddenPair.profile false t 1) := by
  intro h
  have hc:=RightOneLayer.necessary h
  have hf : RightOneLayer.forced driver (fun t=>PeriodicHiddenPair.profile false t 1) 2=true := rfl
  have impossible:=hc.2.1 2 rfl rfl hf
  change false=true at impossible
  cases impossible

theorem block_profile_not_compatible (q : Nat → Bool) :
    ¬RightOneLayer.Compatible driver (fun t=>BlockHiddenPair.profile q true t 1) := by
  intro h
  have hc:=RightOneLayer.necessary h
  have hf : RightOneLayer.forced driver (fun t=>BlockHiddenPair.profile q true t 1) 4=true := by
    unfold RightOneLayer.forced
    dsimp only
    rw [block_left_four]
    rfl
  have impossible:=hc.2.1 4 rfl rfl hf
  change xor (BlockHiddenPair.profile q true 5 1) (driver 6)=true at impossible
  rw [block_left_five] at impossible
  change false=true at impossible
  cases impossible

/-- EVERY schedule in the arbitrary-block family's true branch is incompatible
with the actual center/right recurrence. This uses times 4..6, not a scan bound. -/
theorem block_true_branch_no_extension (q : Nat → Bool) :
    ¬∃ X : Nat → Int → Bool, FullHistory X ∧ (∀ t,X t 0=driver t) ∧
      (∀ t,X t (-1)=BlockHiddenPair.profile q true t 1) := by
  rintro ⟨X,hX,hc,hl⟩
  have h:=three_white_left_black_stays hX 4 0
    (by rw [hc];rfl) (by rw [hc];rfl) (by rw [hc];rfl)
    (by change X 4 (-1)=true;rw [hl];exact block_left_four q)
  change X 5 (-1)=true at h
  rw [hl,block_left_five] at h
  cases h

/-- The finite-H barrier is a driven-half-line barrier, not a pair of actual
full-space histories. Its false branch already fails full compatibility by time4. -/
theorem finite_false_branch_no_extension (H : Nat) (hH : 4≤H) :
    ¬∃ X : Nat → Int → Bool, FullHistory X ∧
      (∀ t,t≤H → X t 0=driver t) ∧
      (∀ t,t≤H → X t (-1)=L (effective driver) (FiniteHiddenPair.cut H false) t (-1)) := by
  rintro ⟨X,hX,hc,hl⟩
  have hleft2 : X 2 (-1)=true := by
    rw [hl 2 (by omega)]
    change L (effective driver) (FiniteHiddenPair.cut H false) 2 (-((1 : Nat) : Int))=true
    rw [FiniteHiddenPair.cut_matches H false 2 (by omega) 1 (by decide) (by decide)]
    rfl
  have hleft3 : X 3 (-1)=false := by
    rw [hl 3 (by omega)]
    change L (effective driver) (FiniteHiddenPair.cut H false) 3 (-((1 : Nat) : Int))=false
    rw [FiniteHiddenPair.cut_matches H false 3 (by omega) 1 (by decide) (by decide)]
    rfl
  have h:=three_white_left_black_stays hX 2 0
    (by rw [hc 2 (by omega)];rfl) (by rw [hc 3 (by omega)];rfl)
    (by rw [hc 4 (by omega)];rfl) hleft2
  change X 3 (-1)=true at h
  rw [hleft3] at h
  cases h

#print axioms three_white_left_black_stays
#print axioms full_history_compatible
#print axioms periodic_profile_not_compatible
#print axioms block_profile_not_compatible
#print axioms periodic_false_branch_no_extension
#print axioms block_true_branch_no_extension
#print axioms finite_false_branch_no_extension
end HiddenPairRightObstruction
