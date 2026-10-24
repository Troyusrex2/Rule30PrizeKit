module

public import Rule30Tail13Chunk00
public import Rule30Tail13Chunk01
public import Rule30Tail13Chunk02
public import Rule30Tail13Chunk03
public import Rule30Tail13Chunk04
public import Rule30Tail13Chunk05
public import Rule30Tail13Chunk06
public import Rule30Tail13Chunk07
public import Rule30Tail13Chunk08
public import Rule30Tail13Chunk09
public import Rule30Tail13Chunk10
public import Rule30Tail13Chunk11
public import Rule30Tail13Chunk12
public import Rule30Tail13Chunk13
public import Rule30Tail13Chunk14
public import Rule30Tail13Chunk15
public import Rule30Tail13Chunk16
public import Rule30Tail13Chunk17
public import Rule30Tail13Chunk18
public import Rule30Tail13Chunk19
public import Rule30Tail13Chunk20
public import Rule30Tail13Chunk21
public import Rule30Tail13Chunk22
public import Rule30Tail13Chunk23
public import Rule30Tail13Chunk24
public import Rule30Tail13Chunk25
public import Rule30Tail13Chunk26
public import Rule30Tail13Chunk27
public import Rule30Tail13Chunk28
public import Rule30Tail13Chunk29
public import Rule30Tail13Chunk30
public import Rule30Tail13Chunk31

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFour

/-! Completes the omitted odd-prefix / tail-13 family in the official
four-tail stripe theorem. The certificate has width 46 and period 2^21.
This is not Q01 or a solution of a prize problem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront Rule30ZeroBoundary

theorem complete_path : PathOK 46 45 1 0 (13, 0) (13, 0) 2097152 :=
  (path_append (path_append (path_append (path_append (path_append path_chunk_00 path_chunk_01) (path_append path_chunk_02 path_chunk_03)) (path_append (path_append path_chunk_04 path_chunk_05) (path_append path_chunk_06 path_chunk_07))) (path_append (path_append (path_append path_chunk_08 path_chunk_09) (path_append path_chunk_10 path_chunk_11)) (path_append (path_append path_chunk_12 path_chunk_13) (path_append path_chunk_14 path_chunk_15)))) (path_append (path_append (path_append (path_append path_chunk_16 path_chunk_17) (path_append path_chunk_18 path_chunk_19)) (path_append (path_append path_chunk_20 path_chunk_21) (path_append path_chunk_22 path_chunk_23))) (path_append (path_append (path_append path_chunk_24 path_chunk_25) (path_append path_chunk_26 path_chunk_27)) (path_append (path_append path_chunk_28 path_chunk_29) (path_append path_chunk_30 path_chunk_31)))))

theorem cycle13_complete : Cycle 46 45 13 0 2097152 :=
  ⟨by decide, by decide, complete_path⟩

theorem row4_13_all_odd (m : Nat) (hq : m % 2 = 1) :
    (∀ k, 1 ≤ k → k < m + 1 → row4 m 13 k = stripe k) ∧
      row4 m 13 (m + 1) ≠ stripe (m + 1) ∧
      ∃ t, t ≤ m + 45 ∧ t % 2 = 0 ∧ zrow (row4 m 13) t 1 = false := by
  have hag : ∀ k, 1 ≤ k → k < m + 1 → row4 m 13 k = stripe k := by
    intro k _ hk; unfold row4; rw [ite_eq_left (by omega)]
  have hdev : row4 m 13 (m + 1) ≠ stripe (m + 1) := by
    unfold row4
    rw [ite_eq_right (by omega), show m + 1 - m - 1 = 0 by omega,
      stripe_add_mod m 1 1 hq]
    decide
  have hwin : pk (fun i => row4 m 13 (m + 1 + i)) 46 = 13 := by
    have hw : pk (fun i => row4 m 13 (m + 1 + i)) 46 = pk (tail4 13) 46 :=
      pk_congr _ _ _ fun i _ => by
        unfold row4
        rw [ite_eq_right (by omega), show m + 1 + i - m - 1 = i by omega]
    rw [hw]; decide +kernel
  have hcyc : Cycle 46 45 (pk (fun i => row4 m 13 (m + 1 + i)) 46)
      ((m + 1) % 2) 2097152 := by
    rw [hwin, show (m + 1) % 2 = 0 by omega]
    exact cycle13_complete
  obtain ⟨s, hs, he, hz⟩ := front_sound (row4 m 13) (m + 1) 46 45 2097152
    (by omega) hag (by omega) hcyc
  exact ⟨hag, hdev, m + s, by omega, by simpa using he, by simpa using hz⟩

theorem stripe_four_tail_complete (m : Nat) (v : Fin 16) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 6 ∧
      (∀ k, 1 ≤ k → k < d → row4 m v.val k = stripe k) ∧
      row4 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row4 m v.val) t 1 = false := by
  by_cases h : v.val ≠ 13 ∨ m % 2 = 0
  · obtain ⟨d, hd, hdm, hag, hdev, t, ht, he, hz⟩ := stripe_four_tail m v h
    exact ⟨d, hd, hdm, hag, hdev, t, by omega, he, hz⟩
  · have hv : v.val = 13 := by omega
    have hq : m % 2 = 1 := by omega
    rw [hv]
    obtain ⟨hag, hdev, t, ht, he, hz⟩ := row4_13_all_odd m hq
    exact ⟨m + 1, by omega, by omega, hag, hdev, t, by omega, he, hz⟩

end Ruliology.CellularAutomata.Rule30Tail13Completion
