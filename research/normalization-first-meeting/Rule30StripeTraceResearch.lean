import Rule30StripePreservationResearch

/-! Stripe-related finite rows have identical entire center traces. The
converse, even allowing a stripe relation at time zero or one, is OPEN. -/

namespace Rule30NormalizationMachineResearch

theorem phiRows_add (a s t : Nat) : phiRows a (s+t) = phiRows (phiRows a s) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change Phi (phiRows a (s+t)) = Phi (phiRows (phiRows a s) t)
      exact congrArg Phi ih

theorem phiRows_two_start (a t : Nat) :
    phiRows (Phi (Phi a)) t = phiRows a (t+2) := by
  have h := (phiRows_add a 2 t).symm
  simpa only [Nat.add_comm 2 t,phiRows] using h

/-- Erasing or replacing a stripe prefix with a common white separator
preserves the entire center trace. This is one direction of the trace-kernel
classification; the converse is not claimed. -/
theorem stripe_related_same_trace (a b c : Nat) (h : StripeRelated a b c) (t : Nat) :
    (phiRows a t).testBit (c+t) = (phiRows b t).testBit (c+t) := by
  induction t using Nat.strongRecOn generalizing a b c with
  | ind t ih =>
      rcases t with _ | t
      · exact h.center_pair.1
      · rcases t with _ | t
        · exact h.center_pair.2
        · have hn : t+1+1 = t+2 := by omega
          rw [hn]
          have hh := ih t (by omega) (Phi (Phi a)) (Phi (Phi b)) (c+2)
            (stripe_related_preserves_two a b c h)
          have hc : (c+2)+t = c+(t+2) := by omega
          simpa only [phiRows_two_start,hc] using hh

theorem stripe_related_same_prefix (a b c t : Nat) (h : StripeRelated a b c) :
    SameCenterPrefix a b c t := fun s _ => stripe_related_same_trace a b c h s

/-- For a pair with equal entire center traces, entering the stripe relation
at any finite time is equivalent to entering it at time zero or one. This
does not assert that such an entry must happen. -/
theorem eventually_stripe_iff_early (a b c : Nat)
    (ht : ∀ t, (phiRows a t).testBit (c+t) = (phiRows b t).testBit (c+t)) :
    (∃ t, StripeRelated (phiRows a t) (phiRows b t) (c+t)) ↔
      StripeRelated a b c ∨ StripeRelated (Phi a) (Phi b) (c+1) := by
  constructor
  · rintro ⟨t,hr⟩
    exact stripe_meeting_is_early a b c t (fun s _ => ht s) hr
  · rintro (h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩

end Rule30NormalizationMachineResearch
