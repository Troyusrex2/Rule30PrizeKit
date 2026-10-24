import Rule30StripeTraceResearch

/-! A limitation on applying whole-history XOR rigidity to center traces.
The paired difference need not itself be a Rule 30 orbit, even when the
initial rows are finite and their entire center traces agree. -/

namespace Rule30NormalizationMachineResearch

theorem two_three_stripe_related : StripeRelated 2 3 1 := by
  apply (rowRelated_iff_stripeRelated 2 3 1).mp
  apply (relationRun_full_iff 2 3 1 4 (zerosFrom_large 2 4 (by decide))
    (zerosFrom_large 3 4 (by decide)) (by decide)).mp
  decide +kernel

theorem two_three_entire_trace :
    ∀ t, (phiRows 2 t).testBit (1+t) = (phiRows 3 t).testBit (1+t) :=
  stripe_related_same_trace 2 3 1 two_three_stripe_related

/-- A kernel-checked counterexample to inferring a valid XOR-difference orbit
from equality of a finite pair's entire center trace. The XOR update already
fails on the first step: Phi(2 XOR 3)=7 but Phi(2) XOR Phi(3)=3. -/
theorem same_trace_does_not_imply_xor_step :
    (∀ t, (phiRows 2 t).testBit (1+t) = (phiRows 3 t).testBit (1+t)) ∧
    Phi (2 ^^^ 3) ≠ (Phi 2 ^^^ Phi 3) := by
  exact ⟨two_three_entire_trace, by decide +kernel⟩

end Rule30NormalizationMachineResearch
