module
public import Ruliology.CellularAutomata.Rule30ResetSwap

/-! Finite witness for the first failed backward lift in undo_witness.py. -/
@[expose] public section
namespace FailedLift
open Ruliology.CellularAutomata.Rule30ZeroBoundary
open IntegerForm

def original := 2440786724530854946624415088918
def altered72 := 10500241303133006747930660018695972033202183908454678

theorem meet111 : iter F 111 original = iter F 39 altered72 := by decide +kernel

theorem two_changes : ∀ i : Fin 40,
    xor ((iter F (72+i.val) original).testBit 0) ((iter F i.val altered72).testBit 0)
      = decide (i.val=34 ∨ i.val=38) := by decide +kernel

/-- Compute two consecutive registers from the least significant bit. -/
def registers (y : Nat) (b : Bool) : Nat → Bool × Bool
  | 0 => (false,b)
  | j+1 => let p := registers y b j
           (p.2, xor (y.testBit j) (p.2 || p.1))

theorem registers_eq (y : Nat) (b : Bool) (j : Nat) :
    registers y b j = (back b (rowOfNat y) j,back b (rowOfNat y) (j+1)) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [registers,ih]; rfl

theorem transfer (y j : Nat) (b : Bool) (h : (registers y b j).2=true) :
    back b (rowOfNat y) (j+1)=true :=
  (congrArg Prod.snd (registers_eq y b j)).symm.trans h

set_option maxRecDepth 8000 in
theorem neither_predecessor_finite (b : Bool) : ¬FinSupp (back b (rowOfNat altered72)) := by
  have zeros : ∀ k, 174≤k → rowOfNat altered72 k=false := by
    intro k hk
    obtain ⟨j,rfl⟩ : ∃ j, k=j+1 := ⟨k-1,by omega⟩
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : altered72<2^173)
      (Nat.pow_le_pow_right (by decide) (by omega : 173≤j)))
  have tab : ∀ wall, (registers altered72 wall 173).2=true := by decide +kernel
  intro hn
  have conflict := ((back_fin_iff b (by decide : 2≤174) zeros).mp hn).2
  have opposite : back b (rowOfNat altered72) 174=true :=
    transfer altered72 173 b (tab b)
  exact Bool.noConfusion (conflict.symm.trans opposite)

end FailedLift
