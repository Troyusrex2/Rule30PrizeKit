import Ruliology.CellularAutomata.Rule30StripeMeeting

/-! Equal complete future traces do not determine the observation one step
earlier, even when both predecessors are positive finite rows. This refutes
an unrestricted backward reduction, not the seed-specific prize statement. -/

namespace Rule30BackwardTraceObstruction

open Ruliology.CellularAutomata.Rule30StripeMeeting

theorem images_stripe_related : StripeRelated (Phi 6) (Phi 5) 1 := by
  change StripeRelated 26 27 1
  refine Or.inr ⟨1, by decide, ?_, ?_, by decide, by decide,
    by decide, by decide, ?_⟩
  · change StripeWord ([false] ++ [true])
    apply StripeWord.single
    intro b hb
    exact List.mem_singleton.mp hb
  · change StripeWord ([] ++ [true,true])
    apply StripeWord.double
    intro b hb
    cases hb
  · intro i hi
    have hq : 26 >>> 1 = 27 >>> 1 := by decide
    have he := congrArg (fun q : Nat => q.testBit (i-1)) hq
    simpa only [Nat.testBit_shiftRight, show 1+(i-1)=i by omega] using he

theorem equal_future_images (t : Nat) :
    (phiRows (Phi 6) t).testBit (1+t) = (phiRows (Phi 5) t).testBit (1+t) :=
  stripe_related_same_trace (Phi 6) (Phi 5) 1 images_stripe_related t

theorem parent_traces_agree_after_one (t : Nat) :
    (phiRows 6 (t+1)).testBit (t+1) = (phiRows 5 (t+1)).testBit (t+1) := by
  have h := equal_future_images t
  change (phiRows (phiRows 6 1) t).testBit (1+t) =
    (phiRows (phiRows 5 1) t).testBit (1+t) at h
  rw [← phiRows_add, ← phiRows_add] at h
  simpa only [Nat.add_comm] using h

theorem different_predecessor_observation : (6 : Nat).testBit 0 ≠ (5 : Nat).testBit 0 := by
  decide +kernel

theorem positive_finite_predecessors : 0 < (6 : Nat) ∧ 0 < (5 : Nat) := by decide

theorem same_predecessor_edge : Nat.log2 6 = 2 ∧ Nat.log2 5 = 2 := by decide

theorem no_unrestricted_backward_rule :
    ¬ (∀ a b c : Nat, 0 < a → 0 < b →
      (∀ t, (phiRows (Phi a) t).testBit (c+1+t) =
            (phiRows (Phi b) t).testBit (c+1+t)) → a.testBit c = b.testBit c) := by
  intro h
  exact different_predecessor_observation (h 6 5 0 (by decide) (by decide) equal_future_images)

end Rule30BackwardTraceObstruction
