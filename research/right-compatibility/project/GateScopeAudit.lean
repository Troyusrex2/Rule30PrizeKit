module
public import PeriodTwoGateExclusion
@[expose] public section
namespace GateScopeAudit
open PeriodTwoGateExclusion

/-- The exact eight-bit set used by the earlier CP* scripts, in low-time bit order. -/
def S : List Nat := [8,9,16,18,33,36,66,72,132,144]

set_option maxRecDepth 4096 in
theorem s_excludes_complement_certificate : ∀ w : Fin 256, w.val∈S →
    ∃ j : Fin 6, (!(w.val.testBit j.val)) ≠ word j.val := by decide

/-- A local S window, without claiming that all actual right histories are S-legal. -/
def SWindow (g : Nat → Bool) (t : Nat) : Prop :=
  ∃ w : Fin 256,w.val∈S ∧ ∀ j : Fin 8,w.val.testBit j.val=g (t+j.val)

/-- The new arbitrary-right010110 exclusion adds nothing to an existing S window
after the complement/phase conversion f(n)=NOT g(n+1). -/
theorem s_already_excludes (g : Nat → Bool) (t : Nat) (hs : SWindow g t) :
    ¬(∀ j,j<6 → (!g (t+j))=word j) := by
  rintro h
  obtain ⟨w,hw,hbits⟩:=hs
  obtain ⟨j,hj⟩:=s_excludes_complement_certificate w hw
  have hb:=hbits ⟨j.val,by omega⟩
  rw [hb] at hj
  exact hj (h j.val j.isLt)

#print axioms s_already_excludes
end GateScopeAudit
