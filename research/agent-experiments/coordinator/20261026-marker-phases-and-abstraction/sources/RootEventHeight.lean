import Ruliology.CellularAutomata.Rule30Prize
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! Exact integer signed event-height identities for arbitrary Boolean drivers.
No finite-white ancestry, D3*, or converse from unmarked height oscillation
is asserted. The safety consequence retains the initial orientation sign. -/
namespace RootEventHeight
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def bit (v : Bool) : Int := if v then 1 else 0
def white (v : Bool) : Int := if v then 0 else 1
def sign (t : Nat) : Int := (-1 : Int)^t
def zeroPair (a b : Nat → Bool) (t : Nat) : Bool := (!a t) && (!b t)
def event (a b x : Nat → Bool) (t : Nat) : Bool := zeroPair a b t && (!x t)
def q (x : Nat → Bool) (t : Nat) : Int := sign t * (2*white (x t)-1)
def height (A : Nat → Bool) (T : Nat) : Int := ∑ t ∈ Finset.range T, sign t * bit (A t)
def Recurrence (a b x : Nat → Bool) : Prop := ∀ t,
  x (t+1)=xor (x t) (a t || b t)
def Safe (x : Nat → Bool) : Prop := ∀ t,
  ¬ (x t=false ∧ x (t+1)=false)

theorem sign_succ (t : Nat) : sign (t+1) = -sign t := by
  simp [sign,pow_succ]

theorem sign_cases (t : Nat) : sign t=1 ∨ sign t= -1 := by
  induction t with
  | zero => exact Or.inl rfl
  | succ t ih =>
    rw [sign_succ]
    rcases ih with h|h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h]; rfl)

theorem sign_even (T : Nat) (h : Even T) : sign T=1 := by
  obtain ⟨k,hk⟩ := h
  rw [hk,show k+k=2*k by omega]
  simp [sign,pow_mul]

theorem q_cases (x : Nat → Bool) (t : Nat) : q x t=1 ∨ q x t= -1 := by
  rcases sign_cases t with h|h <;> cases hx : x t <;> simp [q,white,h,hx]

theorem q_zero (x : Nat → Bool) : q x 0 = if x 0 then -1 else 1 := by
  cases hx : x 0 <;> simp [q,white,sign,hx]

theorem white_local : ∀ a b x : Bool,
    white x + white (xor x (a || b))-1 =
      2*bit ((!a && !b) && !x)-bit (!a && !b) := by
  decide +kernel

theorem white_step (a b x : Nat → Bool) (h : Recurrence a b x) (t : Nat) :
    white (x t)+white (x (t+1))-1 = 2*bit (event a b x t)-bit (zeroPair a b t) := by
  rw [h t]
  exact white_local (a t) (b t) (x t)

theorem q_step (a b x : Nat → Bool) (h : Recurrence a b x) (t : Nat) :
    q x (t+1)-q x t = 2*sign t*(bit (zeroPair a b t)-2*bit (event a b x t)) := by
  calc
    q x (t+1)-q x t = -2*sign t*(white (x t)+white (x (t+1))-1) := by
      unfold q
      rw [sign_succ]
      ring
    _ = -2*sign t*(2*bit (event a b x t)-bit (zeroPair a b t)) := by rw [white_step a b x h t]
    _ = 2*sign t*(bit (zeroPair a b t)-2*bit (event a b x t)) := by ring

theorem height_zero (A : Nat → Bool) : height A 0=0 := by simp [height]

theorem height_succ (A : Nat → Bool) (T : Nat) :
    height A (T+1)=height A T + sign T*bit (A T) := by
  exact Finset.sum_range_succ _ T

/-- Exact telescoping for every finite T, entirely over the integers. -/
theorem signed_height_identity (a b x : Nat → Bool) (h : Recurrence a b x) (T : Nat) :
    2*(height (zeroPair a b) T - 2*height (event a b x) T) = q x T-q x 0 := by
  induction T with
  | zero => simp [height_zero]
  | succ T ih =>
    rw [height_succ,height_succ]
    calc
      2*(height (zeroPair a b) T + sign T*bit (zeroPair a b T) -
          2*(height (event a b x) T + sign T*bit (event a b x T))) =
          2*(height (zeroPair a b) T-2*height (event a b x) T) +
            2*sign T*(bit (zeroPair a b T)-2*bit (event a b x T)) := by ring
      _ = (q x T-q x 0)+(q x (T+1)-q x T) := by rw [ih,q_step a b x h T]
      _ = q x (T+1)-q x 0 := by ring

/-- Even parity and return of the child alone suffice; no driver period is
needed for this endpoint version of the signed-sum corollary. -/
theorem even_return_signed_sums (a b x : Nat → Bool) (h : Recurrence a b x)
    (P : Nat) (hp : Even P) (hx : x P=x 0) :
    height (zeroPair a b) P=2*height (event a b x) P := by
  have hi := signed_height_identity a b x h P
  have hq : q x P=q x 0 := by
    unfold q
    rw [sign_even P hp,hx]
    rfl
  rw [hq] at hi
  omega

theorem even_period_signed_sums (a b x : Nat → Bool) (h : Recurrence a b x)
    (P : Nat) (hp : Even P) (hx : ∀ t, x (t+P)=x t) :
    height (zeroPair a b) P=2*height (event a b x) P :=
  even_return_signed_sums a b x h P hp (by simpa using hx 0)

/-- The correction's two values retain the initial sign q(0). -/
theorem marked_correction_range (a b x : Nat → Bool) (h : Recurrence a b x) (T : Nat) :
    height (zeroPair a b) T-2*height (event a b x) T=0 ∨
      height (zeroPair a b) T-2*height (event a b x) T= -q x 0 := by
  have hi := signed_height_identity a b x h T
  rcases q_cases x T with ht|ht <;> rcases q_cases x 0 with hz|hz <;> rw [ht,hz] at hi <;> omega

theorem event_local : ∀ a b x : Bool,
    ((!a && !b) && !x)=true ↔ x=false ∧ xor x (a || b)=false := by
  decide +kernel

theorem event_iff_zero_pair (a b x : Nat → Bool) (h : Recurrence a b x) (t : Nat) :
    event a b x t=true ↔ x t=false ∧ x (t+1)=false := by
  rw [h t]
  exact event_local (a t) (b t) (x t)

theorem safe_event_zero (a b x : Nat → Bool) (h : Recurrence a b x) (hs : Safe x) (t : Nat) :
    event a b x t=false := by
  cases he : event a b x t with
  | false => rfl
  | true => exact False.elim (hs t ((event_iff_zero_pair a b x h t).mp he))

theorem safe_event_height_zero (a b x : Nat → Bool) (h : Recurrence a b x) (hs : Safe x)
    (T : Nat) : height (event a b x) T=0 := by
  simp [height,safe_event_zero a b x h hs,bit]

/-- Safety forces two adjacent signed heights with the orientation mark.
No converse from an unmarked oscillation bound is claimed. -/
theorem safe_marked_height_range (a b x : Nat → Bool) (h : Recurrence a b x) (hs : Safe x)
    (T : Nat) : height (zeroPair a b) T=0 ∨ height (zeroPair a b) T= -q x 0 := by
  simpa only [safe_event_height_zero a b x h hs T,mul_zero,sub_zero] using
    marked_correction_range a b x h T

theorem safe_height_white_initial (a b x : Nat → Bool) (h : Recurrence a b x) (hs : Safe x)
    (hx : x 0=false) (T : Nat) : height (zeroPair a b) T=0 ∨ height (zeroPair a b) T= -1 := by
  simpa only [q_zero,hx,Bool.false_eq_true,ite_false] using safe_marked_height_range a b x h hs T

theorem safe_height_black_initial (a b x : Nat → Bool) (h : Recurrence a b x) (hs : Safe x)
    (hx : x 0=true) (T : Nat) : height (zeroPair a b) T=0 ∨ height (zeroPair a b) T=1 := by
  simpa only [q_zero,hx,ite_true,neg_neg] using safe_marked_height_range a b x h hs T

end RootEventHeight
