import RootEventHeight

/-! Exact safety criterion with the initial orientation retained.
The drivers are arbitrary histories satisfying the stated recurrence.
No finite-white ancestry or return-completeness claim is made. -/
namespace RootOrientedHeight
open RootEventHeight
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem event_height_zero_of_oriented_range (a b x : Nat → Bool)
    (hr : Recurrence a b x)
    (hh : ∀ T, height (zeroPair a b) T = 0 ∨
      height (zeroPair a b) T = -q x 0) :
    ∀ T, height (event a b x) T = 0 := by
  intro T
  have hi := signed_height_identity a b x hr T
  rcases hh T with hz | hz <;>
    rcases q_cases x 0 with h0 | h0 <;>
    rcases q_cases x T with ht | ht <;> omega

theorem event_zero_of_height_zero (a b x : Nat → Bool)
    (hh : ∀ T, height (event a b x) T = 0) :
    ∀ t, event a b x t = false := by
  intro t
  have he := height_succ (event a b x) t
  rw [hh (t+1),hh t] at he
  cases hv : event a b x t with
  | false => rfl
  | true =>
    rcases sign_cases t with ht | ht <;> simp [hv,bit,ht] at he

theorem safe_of_oriented_height_range (a b x : Nat → Bool)
    (hr : Recurrence a b x)
    (hh : ∀ T, height (zeroPair a b) T = 0 ∨
      height (zeroPair a b) T = -q x 0) : Safe x := by
  have hz := event_zero_of_height_zero a b x
    (event_height_zero_of_oriented_range a b x hr hh)
  intro t hbad
  have he := (event_iff_zero_pair a b x hr t).mpr hbad
  rw [hz t] at he
  contradiction

theorem safe_iff_oriented_height_range (a b x : Nat → Bool)
    (hr : Recurrence a b x) :
    Safe x ↔ ∀ T, height (zeroPair a b) T = 0 ∨
      height (zeroPair a b) T = -q x 0 :=
  ⟨fun hs => safe_marked_height_range a b x hr hs,
    safe_of_oriented_height_range a b x hr⟩

theorem unmarked_range_is_insufficient :
    (∀ T, height (zeroPair (fun _ => false) (fun _ => false)) T = 0 ∨
      height (zeroPair (fun _ => false) (fun _ => false)) T = 1) ∧
    Recurrence (fun _ => false) (fun _ => false) (fun _ => false) ∧
    ¬ Safe (fun _ => false) := by
  have hb : Recurrence (fun _ => false) (fun _ => false) (fun _ => true) :=
    fun _ => rfl
  have hs : Safe (fun _ => true) := by intro t h; cases h.1
  refine ⟨safe_height_black_initial _ _ _ hb hs rfl,fun _ => rfl,?_⟩
  intro h
  exact h 0 ⟨rfl,rfl⟩

end RootOrientedHeight
