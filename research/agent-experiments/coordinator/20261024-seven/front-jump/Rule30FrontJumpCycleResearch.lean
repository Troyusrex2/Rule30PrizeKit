import Rule30FrontJumpExecutionResearch
import Rule30FrontJumpMapResearch
import Rule30ExternalFiveTailAudit

/-! A complete width-46 cycle from a parallel return table, a 32-step table
orbit, and the independently verified punctured width-34 cycle. This source
does not import the earlier two-million-step complete-cycle certificate. -/

namespace Rule30FrontJumpResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundaryStripeFront Rule30ZeroBoundary
open Rule30FrontLanesResearch Rule30FrontLiftResearch

theorem full_jump (u : Nat) (hu : u < 4096) :
    orb 46 65536 (13 ||| (u <<< 34),0) = (13 ||| (jump u <<< 34),0) := by
  have h := initial_run_correct 34 12 13 0 u 65536 (by decide) (by decide) (by decide) hu
  rw [run_full, endpoint_word] at h
  exact h

theorem prefix_jump (u : Nat) (hu : u < 4096) :
    orb 46 61005 (13 ||| (u <<< 34),0) = (prefixWord u,1) := by
  have h := initial_run_correct 34 12 13 0 u 61005 (by decide) (by decide) (by decide) hu
  rw [run_prefix] at h
  exact h

theorem block_orbit (j : Nat) :
    orb 46 (65536*j) (13,0) = (13 ||| (jrun j 0 <<< 34),0) := by
  induction j with
  | zero => simp [orb, jrun]
  | succ j ih =>
    rw [Nat.mul_succ, orb_add, ih]
    exact full_jump (jrun j 0) (jrun_lt j 0 (by decide))

theorem period_return : orb 46 2097152 (13,0) = (13,0) := by
  have h := block_orbit 32
  rw [return_cycle] at h
  simpa using h

theorem all_rare (r : Nat) (hr : r < 2097152) (he : r%65536 = 61005) :
    sig 46 r (orb 46 r (13,0)).1 = true := by
  let j := r/65536
  have hj : j < 32 := by dsimp [j]; omega
  have hd : r = 65536*j+61005 := by dsimp [j]; omega
  rw [hd, orb_add, block_orbit j, prefix_jump _ (jrun_lt j 0 (by decide))]
  exact rare_table_sound j hj

theorem compressed_cycle : Cycle 46 45 13 0 2097152 := by
  refine punctured_cycle_lift
    (Klo := 34) (Khi := 46) (Slo := 33) (Shi := 45)
    (A := 13) (B := 13) (p := 0) (L := 65536) (H := 2097152)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ => rfl)
    (by decide) (by decide) Rule30Submission.cyc13_period
    (by decide) (by decide) period_return (fun r => r = 61005) ?_ ?_
  · intro r hr hp hne
    exact Rule30Submission.cyc13_sig r hr hp hne
  · intro r hr _ he
    exact all_rare r hr he

theorem compressed_row4_13 (m : Nat) (hq : m%2 = 1) :
    ∃ t, t ≤ m+45 ∧ t%2 = 0 ∧ zrow (row4 m 13) t 1 = false := by
  have hag : ∀ k, 1 ≤ k → k < m+1 → row4 m 13 k = stripe k := by
    intro k _ hk
    unfold row4
    rw [ite_eq_left (by omega)]
  have hwin : pk (fun i => row4 m 13 (m+1+i)) 46 = 13 := by
    have hw : pk (fun i => row4 m 13 (m+1+i)) 46 = pk (tail4 13) 46 :=
      pk_congr _ _ _ fun i _ => by
        unfold row4
        rw [ite_eq_right (by omega), show m+1+i-m-1 = i by omega]
    rw [hw]
    decide +kernel
  have hc : Cycle 46 45 (pk (fun i => row4 m 13 (m+1+i)) 46) ((m+1)%2) 2097152 := by
    rw [hwin, show (m+1)%2 = 0 by omega]
    exact compressed_cycle
  obtain ⟨s, hs, he, hz⟩ := front_sound (row4 m 13) (m+1) 46 45 2097152
    (by omega) hag (by omega) hc
  exact ⟨m+s, by omega, by simpa using he, by simpa using hz⟩

end Rule30FrontJumpResearch
