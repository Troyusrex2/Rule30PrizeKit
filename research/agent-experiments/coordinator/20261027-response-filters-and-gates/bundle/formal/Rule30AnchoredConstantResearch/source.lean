module
public import Rule30CAObserverResearch

/-! A black first column excludes constant later columns in the genuine
sheared recurrence. The application concerns the literal finite tail CA
observer; no fixed physical-center statement is asserted. -/
@[expose] public section
namespace Rule30AnchoredConstantResearch
open Rule30CommonPastResearch Rule30ReaderCanonicalResearch Rule30CAObserverResearch
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Any constant column beyond depth zero would force its predecessor
white forever, contradicting the black anchor by induction on depth. -/
theorem no_constant_after_black (a : Nat → Nat → Bool) (ha : Actual a)
    (h0 : ∀ t, a t 0=true) (j : Nat) (hj : 0<j) (b : Bool) :
    ¬ ∀ t, a t j=b := by
  induction j generalizing b with
  | zero => omega
  | succ j ih =>
      intro hc
      cases j with
      | zero =>
          have hs := ha 0 1
          change a 1 1=xor (a 0 1) (a 0 0) at hs
          rw [hc 1,hc 0,h0 0] at hs
          cases b <;> contradiction
      | succ j =>
          apply ih (by omega) false
          intro t
          have hs := ha t (j+2)
          change a (t+1) (j+2)=xor (a t (j+2)) (a t (j+1) || a t j) at hs
          rw [hc (t+1),hc t] at hs
          cases hp : a t (j+1) with
          | false => rfl
          | true =>
              rw [hp] at hs
              cases b <;> cases a t j <;> contradiction

theorem last_take (x : Nat → Bool) (n : Nat) (d : Bool) :
    lastBit d (takeBits x (n+1))=x n := by
  induction n generalizing x d with
  | zero => rfl
  | succ n ih =>
      change lastBit (x 0) (takeBits (fun j => x (j+1)) (n+1))=x (n+1)
      exact ih (fun j => x (j+1)) (x 0)

theorem trace_full (xs : List Bool) (hn : 0<xs.length) (t : Nat) :
    trace xs t=full xs t (xs.length-1) := by
  unfold trace r
  rw [← prefix_full]
  cases hlen : xs.length with
  | zero => omega
  | succ n => exact last_take (full xs t) n false

theorem word0_first_black (xs : List Bool) (t : Nat) : full (word0 xs) t 0=true := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

/-- The two CA observation channels of a nonempty finite tail cannot both
be black at every time. No observer injectivity premise is used. -/
theorem not_always_black (xs : List Bool) (hx : xs≠[]) :
    ¬ ∀ t, r (titer xs t)=true ∧ s (titer xs t)=true := by
  intro hc
  have ht : ∀ t, trace (word0 xs) t=true := by
    intro t
    have hr := Nat.mod_lt t (by decide : 0<2)
    by_cases hm : t%2=0
    · have he : t=2*(t/2) := by omega
      rw [he,trace_even]
      exact (hc _).1
    · have he : t=2*(t/2)+1 := by omega
      rw [he,trace_odd hx]
      exact (hc _).2
  have hn : 0<(word0 xs).length := by simp [word0]
  apply no_constant_after_black (full (word0 xs)) (full_actual _) (word0_first_black xs)
    ((word0 xs).length-1) (by simp [word0]) true
  intro t
  rw [← trace_full _ hn]
  exact ht t

end Rule30AnchoredConstantResearch
