module
public import Ruliology.CellularAutomata.Rule30InverseCascade
@[expose] public section
open Ruliology.CellularAutomata
open Rule30InverseCascade

-- Transfer and forward dynamics are the official Rule30 definitions.
example (b : Bool) (s : State) : transfer b s=Rule30.T b s := rfl
example (a : Nat → Bool) (k : Nat) :
    forward a k=Rule30.rule (a (k+2)) (a (k+1)) (a k) := rfl

-- Check complete quantified headline types, not just their names.
example : ∀ (m : Nat) (driver : Nat → Bool) (X : Nat → Nat → (Bool × Bool)),
    (∀ i,i<m → ∀ k,X i (k+1)=Rule30.T
      (if i+1<m then (X (i+1) k).2 else driver k) (X i k)) →
    (∀ i,i<m → TailClosing (fun k =>
      if i+1<m then (X (i+1) k).2 else driver k)) →
    ∃ K,∀ Y : Nat → Nat → (Bool × Bool),
      (∀ i,i<m → ∀ k,Y i (k+1)=Rule30.T
        (if i+1<m then (Y (i+1) k).2 else driver k) (Y i k)) →
      ∀ i,i<m → ∀ k,K≤k → X i k=Y i k := finite_cascade_closes

example : ∀ (a : Nat → Nat → Bool),
    (∀ i,a (i+1)=fun k => Rule30.rule (a i (k+2)) (a i (k+1)) (a i k)) →
    (∀ i,TailClosing (fun k => Rule30.rule (a i (k+2)) (a i (k+1)) (a i k))) →
    ∀ m,∃ K,∀ Y : Trajectory,StackLaw m (a m) Y →
      ∀ i,i<m → ∀ k,K≤k → Y i k=(a i (k+1),a i k) := physical_block_closes

example : ∀ (m : Nat) (driver : Nat → Bool) (X : Trajectory) (K : Nat → Nat),
    StackLaw m driver X → ResetSchedule m driver X K →
    ∀ Y : Trajectory,StackLaw m driver Y →
      ∀ i,i<m → ∀ k,K m≤k → X i k=Y i k := by
  intro m driver X K law schedule
  exact scheduled_cascade_closes m driver X law K schedule

example : ∀ (m : Nat) (driver : Nat → Bool) (X : Trajectory),
    DriversClosing m driver X → ∀ start,
    ∃ K : Nat → Nat,K 0=start ∧ ResetSchedule m driver X K := exists_reset_schedule

example : ∀ (k : Nat) (last : Bool),
    Synchronized ([false]++List.replicate (3*k+1) true++[false,last]) := run_resets
