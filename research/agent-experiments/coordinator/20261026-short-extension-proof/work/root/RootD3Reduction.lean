import RootShortExtension
import CedarWhiteTransport

/-! A precise open ancestry target and its conditional global consequence.
No theorem in this module asserts D3Star. Leading white padding is removed
using the literal finite-white evolution, not by changing its boundary. -/
namespace RootD3Reduction
open CedarSafetySoundness CedarSafety CedarSafetyBridge
open CedarWhiteTransport RootShortExtension
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Normalized D3*: every safe word beginning with its first black cell,
with effective length at least four, has a safe prefix at distance 1, 2,
or 3 from the newest end. There is no return-period premise. -/
def D3Star : Prop := ∀ ys : List Bool, 3 ≤ ys.length → Safe (true :: ys) →
  ∃ u v : List Bool, true :: ys = u ++ v ∧ Safe u ∧ 1 ≤ v.length ∧ v.length ≤ 3

def ReturnComplete : Prop := ∀ xs : List Bool, Safe xs → evolution 8 xs = xs

theorem small_return (xs : List Bool) (h : xs.length ≤ 3) : evolution 8 xs = xs := by
  obtain ⟨k,hk⟩ := RootShortExtensionCertificate.shortWord_complete xs h
  subst xs
  have cert : ∀ k : Fin 15,
      evolution 8 (RootShortExtensionCertificate.shortWord k) =
        RootShortExtensionCertificate.shortWord k := by decide +kernel
  exact cert k

/-- Strong induction on actual finite width. The only unproved premise is
the explicitly stated normalized ancestry implication. -/
theorem return_complete_of_d3 (hd : D3Star) : ReturnComplete := by
  have aux : ∀ n : Nat, ∀ xs : List Bool, xs.length = n → Safe xs → evolution 8 xs = xs := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro xs hn hs
      by_cases hsmall : xs.length ≤ 3
      · exact small_return xs hsmall
      · cases xs with
        | nil => rfl
        | cons b ys =>
          cases b with
          | false =>
            apply (return8_false_cons ys).mpr
            apply ih ys.length (by simp only [List.length_cons] at hn; omega) ys rfl
            exact (safe_false_cons ys).mp hs
          | true =>
            obtain ⟨u,v,huv,hu,hv0,hv3⟩ := hd ys (by simp only [List.length_cons] at hsmall; omega) hs
            have hlength : u.length + v.length = n := by
              simpa only [List.length_append] using (congrArg List.length huv).symm.trans hn
            have hr := ih u.length (by omega) u rfl hu
            rw [huv] at hs ⊢
            exact safe_short_extension u v hu hr hv3 hs
  intro xs hs
  exact aux xs.length xs rfl hs

theorem language_complete_of_d3 (hd : D3Star) :
    ∀ xs : List Bool, Safe xs → accepted (read 0 xs) = true := by
  intro xs hs
  exact (safe_return_iff_accepted xs).mp ⟨hs,return_complete_of_d3 hd xs hs⟩

/-- A failure of global return completeness must violate normalized D3*.
This is a conditional reduction, not an asserted counterexample. -/
theorem not_d3_of_not_return_complete (hn : ¬ ReturnComplete) : ¬ D3Star :=
  fun hd => hn (return_complete_of_d3 hd)

end RootD3Reduction
