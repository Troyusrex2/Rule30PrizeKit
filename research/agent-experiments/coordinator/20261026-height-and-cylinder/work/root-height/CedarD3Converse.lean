import RootD3Reduction

/-! The accepted-language table supplies the converse to normalized D3.
This proves an equivalence of open completeness statements, not either statement. -/
namespace CedarD3Converse
open CedarSafetySoundness CedarSafety CedarSafetyBridge RootD3Reduction
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem positive_state_step :
    ∀ q : Fin 13, 0 < q.val → ∀ b : Bool,
      0 < transition q.val b ∧ transition q.val b < 13 := by
  decide +kernel

theorem accepted_three_certificate :
    ∀ q : Fin 13, 0 < q.val → ∀ a b c : Bool,
      accepted (read q.val [a,b,c]) = true →
      accepted q.val = true ∨ accepted (read q.val [a]) = true ∨
        accepted (read q.val [a,b]) = true := by
  decide +kernel

theorem accepted_near_prefix (xs : List Bool) :
    ∀ q : Nat, (0 < q ∧ q < 13) → 3 ≤ xs.length →
      accepted (read q xs) = true →
      ∃ u v : List Bool, xs = u ++ v ∧ accepted (read q u) = true ∧
        1 ≤ v.length ∧ v.length ≤ 3 := by
  induction xs with
  | nil =>
      intro q hq hlen
      simp at hlen
  | cons a xs ih =>
      intro q hq hlen hacc
      by_cases htail : 3 ≤ xs.length
      · have hstep := positive_state_step ⟨q,hq.2⟩ hq.1 a
        obtain ⟨u,v,huv,hu,hv1,hv3⟩ := ih (transition q a) hstep htail hacc
        refine ⟨a :: u,v,?_,hu,hv1,hv3⟩
        rw [huv]
        rfl
      · cases xs with
        | nil => simp at hlen
        | cons b xs =>
          cases xs with
          | nil => simp at hlen
          | cons c xs =>
            cases xs with
            | nil =>
              obtain h0 | h1 | h2 := accepted_three_certificate ⟨q,hq.2⟩ hq.1 a b c hacc
              · exact ⟨[],[a,b,c],rfl,h0,by simp,by simp⟩
              · exact ⟨[a],[b,c],rfl,h1,by simp,by simp⟩
              · exact ⟨[a,b],[c],rfl,h2,by simp,by simp⟩
            | cons d xs => simp at htail

theorem accepted_normalized_safe_prefix (ys : List Bool) (hlen : 3 ≤ ys.length)
    (ha : accepted (read 0 (true :: ys)) = true) :
    ∃ u v : List Bool, true :: ys = u ++ v ∧ Safe u ∧
      1 ≤ v.length ∧ v.length ≤ 3 := by
  change accepted (read 1 ys) = true at ha
  obtain ⟨u,v,huv,hu,hv1,hv3⟩ :=
    accepted_near_prefix ys 1 ⟨by decide,by decide⟩ hlen ha
  have hau : accepted (read 0 (true :: u)) = true := hu
  have hsu : Safe (true :: u) := ((safe_return_iff_accepted (true :: u)).mpr hau).1
  refine ⟨true :: u,v,?_,hsu,hv1,hv3⟩
  rw [huv]
  rfl

theorem d3_of_return_complete (hc : ReturnComplete) : D3Star := by
  intro ys hlen hs
  apply accepted_normalized_safe_prefix ys hlen
  exact (safe_return_iff_accepted (true :: ys)).mp ⟨hs,hc (true :: ys) hs⟩

theorem d3_iff_return_complete : D3Star ↔ ReturnComplete :=
  ⟨return_complete_of_d3,d3_of_return_complete⟩

end CedarD3Converse
