import Rule30NormalizationMachineResearch

/-! All-input machine soundness. Companion modules connect this layer to
actual integer rows and the stripe relation. Numerical-normalizer equivalence
and infinite-trace completeness are not proved. -/

namespace Rule30NormalizationMachineResearch

theorem all_of_member {p : StateTree} {f : Nat → Bool}
    (ha : allNodes p f = true) {s : Nat} (hm : member p s = true) : f s = true := by
  induction p generalizing s with
  | nil => simp [member] at hm
  | node k l r ihl ihr =>
      have hk := (Bool.and_eq_true_iff.mp ha).1
      have hc := (Bool.and_eq_true_iff.mp ha).2
      by_cases he : s = k
      · simpa only [he] using hk
      · by_cases hl : s < k
        · apply ihl (Bool.and_eq_true_iff.mp hc).1
          simpa [member, he, hl] using hm
        · apply ihr (Bool.and_eq_true_iff.mp hc).2
          simpa [member, he, hl] using hm

theorem initial_member : member pool initial = true := (Bool.and_eq_true_iff.mp checked).1

theorem good_of_member {s : Nat} (hs : member pool s = true) : endGood s = true := by
  have all := (Bool.and_eq_true_iff.mp checked).2
  exact (Bool.and_eq_true_iff.mp (all_of_member all hs)).2

theorem step_member {s v e : Nat} (hs : member pool s = true) (hv : v < 8)
    (he : step s v = some e) : member pool e = true := by
  have all := (Bool.and_eq_true_iff.mp checked).2
  have hc := (Bool.and_eq_true_iff.mp (all_of_member all hs)).1
  have h := List.all_eq_true.mp hc v (List.mem_range.mpr hv)
  rw [he] at h
  exact h

def run (s : Nat) : List Nat → Option Nat
  | [] => some s
  | v :: vs => (step s v).bind (fun e => run e vs)

theorem run_member {word : List Nat} {s e : Nat} (hs : member pool s = true)
    (hv : ∀ v, v ∈ word → v < 8) (hr : run s word = some e) : member pool e = true := by
  induction word generalizing s with
  | nil =>
      simp only [run, Option.some.injEq] at hr
      subst hr
      exact hs
  | cons v vs ih =>
      cases hstep : step s v with
      | none => simp [run, hstep] at hr
      | some next =>
          have hnext := step_member hs (hv v (by simp)) hstep
          apply ih hnext
          · intro u hu
            exact hv u (by simp [hu])
          · simpa only [run, hstep, Option.bind_some] using hr

/-- Every length of valid input stays outside the machine's forbidden end set.
The numerical-normalization interpretation is a separate obligation. -/
theorem all_input_lengths_safe (word : List Nat)
    (hv : ∀ v, v ∈ word → v < 8) {e : Nat} (hr : run initial word = some e) :
    endGood e = true :=
  good_of_member (run_member initial_member hv hr)

end Rule30NormalizationMachineResearch
