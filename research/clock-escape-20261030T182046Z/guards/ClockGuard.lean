module
public import Ruliology.CellularAutomata.Rule30EdgeClock
@[expose] public section
open Ruliology.CellularAutomata.Rule30FrozenRuler
open Ruliology.CellularAutomata.Rule30EdgeClock
example (x : Nat → Bool) (j : Nat) :
    T x (j+2)=xor (x (j+2)) (x (j+1)||x j) := rfl
example : ∀ (j s : Nat),0<j → ∀ x : Nat → Bool,x 0=true →
    ∃ t,t≤(j+1)/2 ∧ iter (s+t) x j≠iter s x j := flip_bound_from
example : ∀ j : Nat,0<j → iter ((j+1)/2) one j=true := seed_at_bound
example : ∀ (j s : Nat),0<j → ∀ (x y : Nat → Bool),x 0=true →
    (∀ i,i<j+1 → x i=y i) → x (j+1)≠y (j+1) →
    ∃ t,t≤(j+1)/2+1 ∧ iter (s+t) x (j+2)≠iter (s+t) y (j+2) := recurrent_excitation

-- Regression control: the excluded lowest digit1 really cannot be included.
def controlX (j : Nat) : Bool := decide (j=0)
def controlY (j : Nat) : Bool := decide (j=0 ∨ j=1)
example : ∀ t,iter t controlX 2=iter t controlY 2 := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    change xor (iter t controlX 2) (iter t controlX 1||iter t controlX 0)=
      xor (iter t controlY 2) (iter t controlY 1||iter t controlY 0)
    rw [iter_zero,iter_zero]
    change xor (iter t controlX 2) (iter t controlX 1||true)=
      xor (iter t controlY 2) (iter t controlY 1||true)
    rw [Bool.or_true,Bool.or_true,ih]

example (j s : Nat) (x y : Nat → Bool) (hx : x 0=true)
    (below : ∀ i,i<j+1 → x i=y i) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+2 ∧
      (iter (s+t) x (j+3)≠iter (s+t) y (j+3) ∨
       iter (s+t) x (j+4)≠iter (s+t) y (j+4)) :=
  recurrent_two_layer_escape j s x y hx below different
