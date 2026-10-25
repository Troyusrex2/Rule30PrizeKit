module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift

/-! Certificate data for the tail-13 completion. A punctured width-34
cycle and 32 parallel upper states certify a width-46 return cycle. -/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

def lanes : Nat := 2^32-1

def seeds : List Nat := [0,1763,2034,2161,1704,2123,1930,2041,2720,2627,3154,3729,2120,2539,3370,985,768,4067,2290,3441,1448,331,2698,249,2976,3395,2898,913,3912,3307,3114,729]

def embedding (j : Nat) : Nat := 13 ||| (seeds.getD j 0 <<< 34)

def nextIndex (j : Nat) : Nat := (j+1)%32

def state000 : LaneState := ⟨13, 0, [0xaaaaaaaa, 0x66666666, 0x0, 0xf0f0f0f0, 0x8c8c8c8c, 0x619e619e, 0xb6aeb6ae, 0xa9d6a9d6, 0x1f3be0c4, 0x9d438bd6, 0x721a4cd6, 0x774e7f28]⟩

def state001 : LaneState := ⟨10083106829, 0, [0xaaaaaaaa, 0x33333333, 0xffffffff, 0xc3c3c3c3, 0x4a4a4a4a, 0x3ac53ac5, 0x86678667, 0xc3c7c3c7, 0xf0650f9a, 0x3ee88272, 0x5caa8b3a, 0xdaed7300]⟩

def state002 : LaneState := ⟨536870925, 0, [0x55555555, 0x99999999, 0x0, 0x2d2d2d2d, 0x25252525, 0x659a659a, 0xb142b142, 0x9b349b34, 0x2e20d1df, 0x65609108, 0x8a4fc6fc, 0x2155b5a5]⟩

def state003 : LaneState := ⟨4177526797, 0, [0xaaaaaaaa, 0x33333333, 0xcccccccc, 0xd2d2d2d2, 0xa2a2a2a2, 0x11ee11ee, 0xb673b673, 0x50235023, 0x4292bd6d, 0xdca2d877, 0xdef86f1d, 0x42e565d2]⟩

def state004 : LaneState := ⟨10737418253, 0, [0xaaaaaaaa, 0x99999999, 0x55555555, 0xf0f0f0f0, 0x64646464, 0x6f906f90, 0xa01ea01e, 0x8ae88ae8, 0xceb73148, 0xc5235c91, 0x4266ffa4, 0xb8d190b1]⟩

def state005 : LaneState := ⟨3640655885, 0, [0x55555555, 0xcccccccc, 0xaaaaaaaa, 0x3c3c3c3c, 0xe5e5e5e5, 0x837c837c, 0xe349e349, 0x872a872a, 0xc2273dd8, 0x59be45c1, 0x9a7c0f73, 0x7ae2cbc7]⟩

def state006 : LaneState := ⟨15569256461, 0, [0xaaaaaaaa, 0xcccccccc, 0x0, 0xa5a5a5a5, 0x94949494, 0x53ac53ac, 0x72f572f5, 0x730a730a, 0xb95546aa, 0xcf074383, 0xe1229983, 0xe7abd7a9]⟩

def state007 : LaneState := ⟨14914945037, 0, [0x55555555, 0x33333333, 0x33333333, 0x96969696, 0x43434343, 0x3dc23dc2, 0x4a4c4a4c, 0x9d709d70, 0x28e9d716, 0xfdb1b404, 0xe46265ee, 0x432a2427]⟩

def state008 : LaneState := ⟨4159956310, 1, [0xaaaaaaaa, 0xcccccccc, 0xdddddddd, 0x1e1e1e1e, 0xc4c4c4c4, 0x4ab54ab5, 0x87ba87ba, 0xce91ce91, 0xe2f81d07, 0x5cc7b599, 0xe1219f63, 0x83662450]⟩

def state009 : LaneState := ⟨13, 0, [0x55555555, 0x33333333, 0x0, 0x78787878, 0x46464646, 0x30cf30cf, 0x5b575b57, 0x54eb54eb, 0xf9df062, 0x4ea1c5eb, 0x390d266b, 0x3ba73f94]⟩

theorem run_00 : run 34 lanes 8192 state000 = state001 := by decide +kernel

theorem run_01 : run 34 lanes 8192 state001 = state002 := by decide +kernel

theorem run_02 : run 34 lanes 8192 state002 = state003 := by decide +kernel

theorem run_03 : run 34 lanes 8192 state003 = state004 := by decide +kernel

theorem run_04 : run 34 lanes 8192 state004 = state005 := by decide +kernel

theorem run_05 : run 34 lanes 8192 state005 = state006 := by decide +kernel

theorem run_06 : run 34 lanes 8192 state006 = state007 := by decide +kernel

theorem run_07 : run 34 lanes 3661 state007 = state008 := by decide +kernel

theorem run_08 : run 34 lanes 4531 state008 = state009 := by decide +kernel

theorem run_prefix : run 34 lanes 61005 state000 = state008 :=
  (run_chain (run_chain (run_chain run_00 run_01) (run_chain run_02 run_03)) (run_chain (run_chain run_04 run_05) (run_chain run_06 run_07)))

theorem run_full : run 34 lanes 65536 state000 = state009 :=
  (run_chain (run_chain (run_chain run_00 run_01) (run_chain run_02 run_03)) (run_chain (run_chain run_04 run_05) (run_chain run_06 (run_chain run_07 run_08))))

def prefixWord (j : Nat) : Nat := word 34 (project j state008)

theorem initial_words : (List.range 32).all (fun j =>
    word 34 (project j state000) == embedding j) = true := by decide +kernel

theorem endpoint_words : (List.range 32).all (fun j =>
    word 34 (project j state009) == embedding (nextIndex j)) = true := by decide +kernel

theorem initial_word (j : Nat) (hj : j < 32) : word 34 (project j state000) = embedding j :=
  Nat.beq_eq.mp (List.all_eq_true.mp initial_words j (List.mem_range.mpr hj))

theorem endpoint_word (j : Nat) (hj : j < 32) : word 34 (project j state009) = embedding (nextIndex j) :=
  Nat.beq_eq.mp (List.all_eq_true.mp endpoint_words j (List.mem_range.mpr hj))

theorem rare_table : (List.range 32).all (fun j =>
    sig 46 (65536*j+61005) (prefixWord j)) = true := by decide +kernel

theorem rare_table_sound (j : Nat) (hj : j < 32) :
    sig 46 (65536*j+61005) (prefixWord j) = true :=
  List.all_eq_true.mp rare_table j (List.mem_range.mpr hj)

theorem return_cycle : iter nextIndex 32 0 = 0 := by decide +kernel

theorem index_table : (List.range 32).all (fun j => iter nextIndex j 0 == j) = true := by decide +kernel

theorem iter_index (j : Nat) (hj : j < 32) : iter nextIndex j 0 = j :=
  Nat.beq_eq.mp (List.all_eq_true.mp index_table j (List.mem_range.mpr hj))

theorem lanes_bit (j : Nat) (hj : j < 32) : lanes.testBit j = true := by
  unfold lanes
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

theorem seg13_0 : seg 34 33 1 536870925 0 16384 0 13 0 = true := by decide +kernel
theorem seg13_1 : seg 34 33 1 10737418253 0 16384 16384 536870925 0 = true := by decide +kernel
theorem seg13_2 : seg 34 33 1 15569256461 0 16384 32768 10737418253 0 = true := by decide +kernel
theorem seg13_3 : seg 34 33 1 4159956310 1 11853 49152 15569256461 0 = true := by decide +kernel
theorem seg13_4 : seg 34 33 1 13 0 4530 61006 13020969643 0 = true := by decide +kernel

theorem cyc13_part1 : PathOK 34 33 1 0 (13, 0) (4159956310, 1) 61005 :=
  path_append (path_append (path_append
    (seg_sound 34 33 1 536870925 0 16384 0 13 0 seg13_0)
    (seg_sound 34 33 1 10737418253 0 16384 16384 536870925 0 seg13_1))
    (seg_sound 34 33 1 15569256461 0 16384 32768 10737418253 0 seg13_2))
    (seg_sound 34 33 1 4159956310 1 11853 49152 15569256461 0 seg13_3)

theorem cyc13_step61005 : orb 34 1 (4159956310, 1) = (13020969643, 0) := by decide

theorem cyc13_part2 : PathOK 34 33 1 61006 (13020969643, 0) (13, 0) 4530 :=
  seg_sound 34 33 1 13 0 4530 61006 13020969643 0 seg13_4

theorem cyc13_period : orb 34 65536 (13, 0) = (13, 0) := by
  rw [show (65536 : Nat) = 61005 + 1 + 4530 by decide, orb_add, orb_add,
      cyc13_part1.1, cyc13_step61005, cyc13_part2.1]

/-- **Every odd orbit index `r < 65536` except `r = 61005` satisfies `sig 34 r (orb 34 r (13, 0)).1 = true`.** -/
theorem cyc13_sig (r : Nat) (hr : r < 65536) (hodd : r % 2 = 1) (hne : r ≠ 61005) :
    sig 34 r (orb 34 r (13, 0)).1 = true := by
  by_cases hlt : r < 61005
  · have h := cyc13_part1.2 r hlt (by omega)
    rwa [Nat.zero_add] at h
  · have hgt : 61006 ≤ r := by omega
    obtain ⟨j, rfl⟩ : ∃ j, r = 61006 + j := ⟨r - 61006, by omega⟩
    have hj : j < 4530 := by omega
    have h := cyc13_part2.2 j hj hodd
    rwa [show 61006 + j = 61005 + 1 + j by omega, orb_add, orb_add,
         cyc13_part1.1, cyc13_step61005]


end Ruliology.CellularAutomata.Rule30Tail13Completion
