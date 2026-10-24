import Rule30StripeTraceResearch

/-! A finite, kernel-checked obstruction to the proposed 2*n+2 FULL-row
recovery horizon. This pair has the same left edge, so it does not refute an
edge-only horizon or EdgeObservable. No prize result is claimed. -/

namespace Rule30NormalizationMachineResearch

theorem phiRows_one_start (a t : Nat) : phiRows (Phi a) t = phiRows a (t+1) := by
  have h := (phiRows_add a 1 t).symm
  simpa only [phiRows, Nat.add_comm 1 t] using h

theorem pair58_check : (List.range 58).all (fun t =>
    (phiRows 33 t).testBit (5+t) == (phiRows 45 t).testBit (5+t)) = true := by
  decide +kernel

theorem pair58_prefix : SameCenterPrefix 33 45 5 58 := by
  intro t ht
  exact beq_iff_eq.mp (List.all_eq_true.mp pair58_check t (List.mem_range.mpr ht))

theorem pair58_difference :
    (phiRows 33 58).testBit (5+58) ≠ (phiRows 45 58).testBit (5+58) := by decide +kernel

theorem pair58_no_early_stripe :
    ¬ (StripeRelated 33 45 5 ∨ StripeRelated (Phi 33) (Phi 45) 6) := by
  rintro (h | h)
  · exact pair58_difference (stripe_related_same_trace 33 45 5 h 58)
  · have he := stripe_related_same_trace (Phi 33) (Phi 45) 6 h 57
    apply pair58_difference
    simpa only [phiRows_one_start] using he

theorem linear_full_recovery_counterexample :
    ∃ a b c n : Nat, a < 2^n ∧ b < 2^n ∧ c < n ∧
      SameCenterPrefix a b c (2*n+2) ∧
      ¬ (StripeRelated a b c ∨ StripeRelated (Phi a) (Phi b) (c+1)) := by
  exact ⟨33,45,5,6,by decide,by decide,by decide,
    sameCenterPrefix_mono pair58_prefix (by decide),pair58_no_early_stripe⟩

end Rule30NormalizationMachineResearch
