module
public import Ruliology.CellularAutomata.Rule30Prize
/-! A bounded exact renormalization barrier, not an all-scale impossibility. -/
@[expose] public section
namespace PairFactorBarrier
open Ruliology.CellularAutomata.Rule30Jen
def bit (b : Bool) : Nat := if b then 1 else 0
def middle (w i : Nat) : Bool := rule (w.testBit i) (w.testBit (i+1)) (w.testBit (i+2))
def updatedPair (w : Nat) : Nat :=
  bit (rule (middle w 0) (middle w 1) (middle w 2))+
    2*bit (rule (middle w 1) (middle w 2) (middle w 3))
def projected (h w : Nat) : Bool × Bool × Bool :=
  (h.testBit (w%4),h.testBit ((w/4)%4),h.testBit ((w/16)%4))
def witnesses : List (Nat × Nat) := [(0,0),(4,8),(3,8),(5,16),(6,14),(2,8),(7,8),(13,14),(13,14),(7,8),(2,8),(6,14),(5,16),(3,8),(4,8),(0,0)]
def witness (h : Nat) : Nat × Nat := witnesses.getD h (0,0)
theorem certificates : ∀ h : Fin 16, h.val=0 ∨ h.val=15 ∨
    ((witness h.val).1<64 ∧ (witness h.val).2<64 ∧
      projected h.val (witness h.val).1=projected h.val (witness h.val).2 ∧
      h.val.testBit (updatedPair (witness h.val).1) ≠
        h.val.testBit (updatedPair (witness h.val).2)) := by decide
def eval (f : Bool → Bool → Bool → Bool) (t : Bool × Bool × Bool) : Bool :=
  f t.1 t.2.1 t.2.2
def Factor (h : Nat) (f : Bool → Bool → Bool → Bool) : Prop :=
  ∀ w : Fin 64, h.testBit (updatedPair w.val)=eval f (projected h w.val)
/-- No nonconstant pair-to-bit map makes two Rule30 steps close to one
binary radius-one step. Larger blocks, more states and history are open. -/
theorem no_nonconstant_pair_factor (h : Fin 16) (h0 : h.val≠0) (h1 : h.val≠15) :
    ¬ ∃ f : Bool → Bool → Bool → Bool, Factor h.val f := by
  intro ⟨f,hf⟩
  rcases certificates h with hc|hc|⟨hu,hv,he,hd⟩
  · exact h0 hc
  · exact h1 hc
  · have ha := hf ⟨(witness h.val).1,hu⟩
    have hb := hf ⟨(witness h.val).2,hv⟩
    exact hd (ha.trans ((congrArg (eval f) he).trans hb.symm))
end PairFactorBarrier
