import Rule30StripeTraceResearch

/-! A checked obstruction to two tighter EDGE-only recovery horizons.
The surviving candidate 2*n+2, EdgeObservable, and Problem 1 remain open. -/

namespace Rule30NormalizationMachineResearch

theorem pair13_check : (List.range 13).all (fun t =>
    (phiRows 77 t).testBit (1+t) == (phiRows 56 t).testBit (1+t)) = true := by
  decide +kernel

theorem pair13_prefix : SameCenterPrefix 77 56 1 13 := by
  intro t ht
  exact beq_iff_eq.mp (List.all_eq_true.mp pair13_check t (List.mem_range.mpr ht))

theorem pair13_difference :
    (phiRows 77 13).testBit 14 ≠ (phiRows 56 13).testBit 14 := by decide +kernel

theorem pair13_distinct_edges : Nat.log2 77 = 6 ∧ Nat.log2 56 = 5 := by decide +kernel

/-- A finite counterexample to the proposed `2*n-c` edge horizon, not to
`2*n+2` or to infinite-trace edge observability. -/
theorem edge_horizon_2n_minus_c_counterexample :
    ∃ a b n c : Nat, 0 < a ∧ 0 < b ∧ a < 2^n ∧ b < 2^n ∧ c < n ∧
      SameCenterPrefix a b c (2*n-c) ∧ Nat.log2 a ≠ Nat.log2 b := by
  exact ⟨77,56,7,1,by decide,by decide,by decide,by decide,by decide,
    pair13_prefix,by decide⟩

/-- Even the center-independent horizon `2*n-1` is too short in general. -/
theorem edge_horizon_2n_minus_one_counterexample :
    ∃ a b n c : Nat, 0 < a ∧ 0 < b ∧ a < 2^n ∧ b < 2^n ∧ c < n ∧
      SameCenterPrefix a b c (2*n-1) ∧ Nat.log2 a ≠ Nat.log2 b := by
  exact ⟨77,56,7,1,by decide,by decide,by decide,by decide,by decide,
    pair13_prefix,by decide⟩

end Rule30NormalizationMachineResearch
