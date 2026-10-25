import Rule30RoundTwoDrivenPrefixResearch
import Rule30CriticalChargeOneCoreResearch

namespace Rule30RoundTwoChargeTwoEntryResearch
open Ruliology.CellularAutomata
open Rule30Ether Rule30PeriodTwoCoupled Rule30PeriodTwoSideways Rule30ZeroBoundary
open Rule30RoundTwoDrivenPrefixResearch

def right (p : Nat) : Bool := p==3 || p==7 || p==11
def stream (s : Nat) : Bool := if s<2 then s==1 else s%2==0
def rows : List (List Bool) :=
[
  [true, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, true, false, false, false, false, true, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, true, true, true, true, true, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, true, false, true, true, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, false, false, false, false, true, true, false, true, false, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, true, false, false, true, true, false, false, true, true, true, true, false, true, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, true, true, true, true, false, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, true, false, false, true, false, false, true, true, false, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, false, false, false, false, true, true, true, true, true, true, true, true, false, false, true, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, true, false, false, true, true, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, true, true, true, true, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, true, true, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, true, false, false, true, true, false, false, true, false, true, false, true, true, true, false, true, false, false, false, true, true, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, true, true, true, true, false, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, true, false, false, false, true, false, true, true, false, true, true, false, false, true, false, true, true, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, false, false, false, false, true, true, true, false, true, true, false, true, false, false, true, false, true, true, true, false, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, true, false, false, true, true, false, false, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, false, false, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, true, true, true, true, false, true, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, true, false, true, false, false, false, false, true, false, false, true, true, false, false, true, false, false, true, false, false, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, false, false, false, false, true, true, false, true, true, false, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, true, false, false, true, true, false, false, true, false, true, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, true, true, true, true, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, true, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, true, false, false, false, true, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, false, false, false, false, true, true, true, false, true, true, false, false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, true, false, false, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false, false, false, true, false, false, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false],
  [true, false, false, false, false, true, true, false, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false],
  [false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, false, true, false, true, true, false, false, true, true, true, false, true, true, true, true, false, false, false, false, false],
  [true, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, false, true, true, true, false, true, false, true, true, true, false, false, false, true, false, false, false, true, false, false, false],
  [false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, false, true, true, false, true, false, false, true, false, true, false, false, false, true, false, true, false, false, true, false, true, true, true, false, true, true, true, false],
  [true, false, false, false, false, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false, true, false, false],
  [false, true, false, false, true, true, false, false, false, true, false, false, false, true, false, true, true, true, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true],
  [true, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, false, false, false, true, false, false, false, true, false, false, true, true, true, true, true, true, true, true, true, false, false, true, true, false, false, true, false],
  [false, false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, true, false, false, false, false, false, false, false, false, true, true, true, false, true, true, true],
  [true, false, false, false, false, true, true, false, true, true, false, true, true, true, true, true, false, false, true, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, true, true, false, false, false, true, false],
  [false, true, false, false, true, true, false, false, true, false, false, true, false, false, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, false, true, true],
  [true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, true, false, false, true, false, true],
  [false, false, false, false, false, false, true, false, false, false, false, false, false, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, false],
  [true, false, false, false, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, true, false, false],
  [false, true, false, false, true, true, false, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, false, true, true, true],
  [true, true, true, true, true, false, true, true, true, true, true, true, false, false, true, false, true, false, true, false, true, true, true, true, true, false, true, true, true, true, false, false, true, true, false],
  [false, false, false, false, false, false, true, false, false, false, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false, false, true, false, false, false, true, true, true, false],
  [true, false, false, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, true, false, true, true, false, false, false, true, true, true, false, true, true, false, false],
  [false, true, false, false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, false, false, true, false, true],
  [true, true, true, true, true, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, true, false],
  [false, false, false, false, false, false, true, false, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, true, false, true, false, true, false],
  [true, false, false, false, false, true, true, true, false, true, true, false, false, false, false, true, false, false, false, false, true, false, true, false, true, false, true, false, true],
  [false, true, false, false, true, true, false, false, false, true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, false],
  [true, true, true, true, true, false, true, false, true, true, false, true, true, true, true, false, false, true, true, true, false, false, true, false, true, false, true],
  [false, false, false, false, false, false, true, false, true, false, false, true, false, false, false, true, true, true, false, false, true, true, true, false, true, false],
  [true, false, false, false, false, true, true, false, true, true, true, true, true, false, true, true, false, false, true, true, true, false, false, false, true],
  [false, true, false, false, true, true, false, false, true, false, false, false, false, false, true, false, true, true, true, false, false, true, false, true],
  [true, true, true, true, true, false, true, true, true, true, false, false, false, true, true, false, true, false, false, true, true, true, false],
  [false, false, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, true, true, true, false, false],
  [true, false, false, false, false, true, true, true, false, true, true, false, true, false, true, true, true, false, false, false, true],
  [false, true, false, false, true, true, false, false, false, true, false, false, true, false, true, false, false, true, false, true]
]

theorem right_finite : FinSupp right := by
  refine ⟨11,fun p hp => ?_⟩
  simp [right,show p≠3 by omega,show p≠7 by omega,show p≠11 by omega]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem trace_checked : checkTrace altCol right rows 79 59 = true := by decide +kernel

theorem prefix_sound (t p : Nat) (ht : t≤59) (hp : p<79-t) :
    drv altCol right t p = entry rows t p :=
  trace_sound altCol right rows 79 59 trace_checked t ht p hp

theorem entry_ether : ∀ p, 1≤p → p≤6 →
    drv altCol right 59 p = ether (3+p) (59+3) := by
  intro p hp1 hp6
  rw [prefix_sound 59 p (by decide) (by omega)]
  have hc : (List.range 7).all (fun p => entry rows 59 p == ether (3+p) (59+3)) = true := by decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp hc p (List.mem_range.mpr (by omega)))

theorem entry_wall : ((59+3)%4,rowOf (drv altCol right) 59 6 13) ∈ wallStates := by
  have eq : rowOf (drv altCol right) 59 6 13 = rowOf (entry rows) 59 6 13 := by
    unfold rowOf
    apply seg_congr
    intro i hi
    exact prefix_sound 59 _ (by decide) (by omega)
  rw [eq]
  decide +kernel

theorem driver_ether (t : Nat) : altCol t = ether 3 (t+3) := by
  have h : t%4=0 ∨ t%4=1 ∨ t%4=2 ∨ t%4=3 := by omega
  rcases h with h|h|h|h
  all_goals
    have h2 : t%2 = (t%4)%2 := by omega
    have h4 : (t+3)%4 = (t%4+3)%4 := by omega
    simp [altCol,ether,etherTable,h2,h4,h]

theorem right_col1_after (t : Nat) (ht : 59≤t) :
    drv altCol right t 1 = ether 4 (t+3) := by
  have h0 : ∀ n, 59≤n → drv altCol right n 0 = ether 3 (n+3) := by
    intro n _
    rw [drv_col0,driver_ether]
  have inv := trap_invariant (drv_isR30 altCol right) 3 3 6 59 (by decide)
    h0 entry_ether entry_wall (t-59)
  have hh := inv.1 1 (by decide)
  simpa only [show 59+(t-59)=t by omega] using hh

theorem free_stream (s : Nat) : Rule30CriticalChargeOneCoreResearch.free right s = stream s := by
  rw [Rule30CriticalChargeOneCoreResearch.free,Psi_free]
  by_cases hs : s<29
  · have hc : (List.range 29).all (fun s => (!(entry rows (2*s+1) 1)) == stream s) = true := by decide +kernel
    have hh := beq_iff_eq.mp (List.all_eq_true.mp hc s (List.mem_range.mpr hs))
    rw [prefix_sound (2*s+1) 1 (by omega) (by omega)]
    exact hh
  · rw [right_col1_after (2*s+1) (by omega)]
    have hp : s%2=0 ∨ s%2=1 := Nat.mod_two_eq_zero_or_one s
    rcases hp with hp|hp
    all_goals
      have h4 : (2*s+1+3)%4 = if s%2=0 then 0 else 2 := by split <;> omega
      simp [stream,show ¬s<2 by omega,ether,etherTable,h4,hp]

end Rule30RoundTwoChargeTwoEntryResearch
