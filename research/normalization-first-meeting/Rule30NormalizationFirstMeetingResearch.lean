import Rule30NormalizationTailLanguageResearch

/-! No delayed first meeting in the stripe common-cut relation. Completeness
of this relation for infinite center traces remains OPEN. -/

namespace Rule30NormalizationMachineResearch

def phiRows (a : Nat) : Nat → Nat
  | 0 => a
  | t+1 => Phi (phiRows a t)

def SameCenterPrefix (a b c t : Nat) : Prop :=
  ∀ s, s < t → (phiRows a s).testBit (c+s) = (phiRows b s).testBit (c+s)

theorem sameCenterPrefix_mono {a b c t u : Nat} (h : SameCenterPrefix a b c t)
    (hu : u ≤ t) : SameCenterPrefix a b c u := fun s hs => h s (by omega)

/-- If finite rows become stripe-related after any number of steps, and all
preceding center observations agree, they were stripe-related at time 0 or 1.
The stripe relation is allowed to disappear and reappear; no equivariance
or preservation under Phi is assumed. -/
theorem stripe_meeting_is_early (a b c t : Nat) (ht : SameCenterPrefix a b c t)
    (hr : StripeRelated (phiRows a t) (phiRows b t) (c+t)) :
    StripeRelated a b c ∨ StripeRelated (Phi a) (Phi b) (c+1) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
      rcases t with _ | t
      · exact Or.inl hr
      · rcases t with _ | t
        · exact Or.inr hr
        · have h0 := ht t (by omega)
          have h1 := ht (t+1) (by omega)
          have hh : StripeRelated (Phi (Phi (phiRows a t)))
              (Phi (Phi (phiRows b t))) ((c+t)+2) := by
            simpa only [phiRows, Nat.add_assoc] using hr
          have he := two_step_stripe_related (phiRows a t) (phiRows b t) (c+t)
            h0 (by simpa only [phiRows, Nat.add_assoc] using h1) hh
          rcases he with he | he
          · exact ih t (by omega) (sameCenterPrefix_mono ht (by omega)) he
          · apply ih (t+1) (by omega) (sameCenterPrefix_mono ht (by omega))
            simpa only [phiRows, Nat.add_assoc] using he

/-- The contrapositive is useful for a trace-completeness argument: two rows
not stripe-related at time 0 or 1 cannot become stripe-related later while
their center observations continue to agree. It does not establish that
every equal infinite trace must eventually enter this relation. -/
theorem no_delayed_stripe_meeting (a b c t : Nat)
    (h0 : ¬ StripeRelated a b c)
    (h1 : ¬ StripeRelated (Phi a) (Phi b) (c+1))
    (ht : SameCenterPrefix a b c t) :
    ¬ StripeRelated (phiRows a t) (phiRows b t) (c+t) := by
  intro hr
  rcases stripe_meeting_is_early a b c t ht hr with h | h
  · exact h0 h
  · exact h1 h

end Rule30NormalizationMachineResearch
