import Rule30FrontJumpStatesResearch

/-! Exact algebraic checks on the proposed parallel endpoint table.
The execution certificates separately connect these constants to the orbit. -/

namespace Rule30FrontJumpResearch
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront
open Rule30FrontLanesResearch

def jump (u : Nat) : Nat :=
  pk (fun i => (state009.planes.getD i 0).testBit u) 12

def prefixWord (u : Nat) : Nat := word 34 (project u state008)

def jrun : Nat → Nat → Nat
  | 0, u => u
  | n+1, u => jump (jrun n u)

theorem jump_lt (u : Nat) : jump u < 4096 := by
  change jump u < 2^12
  apply Nat.lt_pow_two_of_testBit _
  intro i hi
  rw [jump, testBit_pk]
  simp [show ¬ (i < 12) by omega]

theorem jrun_lt (n u : Nat) (hu : u < 4096) : jrun n u < 4096 := by
  cases n with
  | zero => exact hu
  | succ n => exact jump_lt _

theorem endpoint_word (u : Nat) : word 34 (project u state009) = 13 ||| (jump u <<< 34) := by
  rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem return_cycle : jrun 32 0 = 0 := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem rare_table : (List.range 32).all (fun j =>
    sig 46 (65536*j+61005) (prefixWord (jrun j 0))) = true := by
  decide +kernel

theorem rare_table_sound (j : Nat) (hj : j < 32) :
    sig 46 (65536*j+61005) (prefixWord (jrun j 0)) = true :=
  List.all_eq_true.mp rare_table j (List.mem_range.mpr hj)

end Rule30FrontJumpResearch
