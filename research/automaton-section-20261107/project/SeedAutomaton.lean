module
public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30Prize

/-!
An exact three-state automaton/dual-word encoding of the ACTUAL singleton
center. This is a reformulation, not an aperiodicity theorem.

The recursion A=(A,C), B=swap(A,C), C=swap(B,C) is automaton 5002 in
Bondarenko et al. arXiv:0803.3555; renaming A->c,B->b,C->a gives 2369.
The external group-theoretic claims are not assumed in any Lean proof here.
-/
@[expose] public section
namespace SeedAutomaton
open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals

inductive St where | A | B | C deriving DecidableEq, Repr
open St
abbrev Stream := Nat → Bool
def flip : St → Bool | A => false | B => true | C => true
def emit (s : St) (b : Bool) := xor b (flip s)
def next : St → Bool → St
  | A,false => A | A,true => C
  | B,false => A | B,true => C
  | C,false => B | C,true => C
def tail (x : Stream) : Stream := fun n => x (n+1)
def cons (b : Bool) (x : Stream) : Stream
  | 0 => b | n+1 => x n
def zero : Stream := fun _ => false
def seed : Stream := cons true zero

def act (s : St) (x : Stream) : Nat → Bool
  | 0 => emit s (x 0)
  | n+1 => act (next s (x 0)) (tail x) n

theorem act_cons (s : St) (b : Bool) (x : Stream) :
    act s (cons b x)=cons (emit s b) (act (next s b) x) := by
  funext n
  cases n <;> rfl

/-- After two input bits, the initial automaton state has no influence. -/
theorem act_local (n : Nat) (s : St) (x : Stream) :
    act s x (n+2)=xor (x (n+2)) (x (n+1) || x n) := by
  induction n generalizing s x with
  | zero =>
    simp only [act,tail]
    cases s <;> cases x 0 <;> cases x 1 <;> cases x 2 <;> rfl
  | succ n ih =>
    change act (next s (x 0)) (tail x) (n+2)=_
    rw [ih]
    rfl

theorem act_A_zero (x : Stream) : act A x 0=x 0 := by
  simp [act,emit,flip]
theorem act_A_one (x : Stream) : act A x 1=xor (x 1) (x 0) := by
  cases h : x 0 <;> simp [act,emit,flip,next,tail,h]

/-- This is the official right-edge frame, with no new trajectory assumed. -/
def row (t : Nat) : Stream := fun j => R j t

theorem act_row (t : Nat) : act A (row t)=row (t+1) := by
  funext j
  cases j with
  | zero => simp [act_A_zero,row,R_zero]
  | succ j =>
    cases j with
    | zero => rw [act_A_one]; simp [row,R_one_succ,R_zero]
    | succ j => exact (act_local j A (row t)).trans (R_step j t).symm

def power (s : St) (x : Stream) : Nat → Stream
  | 0 => x
  | n+1 => act s (power s x n)

theorem power_seed (t : Nat) : power A seed t=row t := by
  induction t with
  | zero =>
    funext j
    cases j with
    | zero => rfl
    | succ j => simp [power,seed,cons,zero,row,R,cell] <;> omega
  | succ t ih => rw [power,ih,act_row]

theorem power_cons_true (n : Nat) :
    power A seed n=cons true (power C zero n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [power,ih,act_cons]; rfl

/-- The index moves with n; replacing it with a fixed index is invalid. -/
theorem center_power (n : Nat) :
    Rule30Prize.center (n+1)=power C zero (n+1) n := by
  have h := congrFun (power_seed (n+1)) (n+1)
  rw [power_cons_true] at h
  change power C zero (n+1) n=R (n+1) (n+1) at h
  simpa [Rule30Prize.center,R] using h.symm

/-- Words act left-to-right: the head state acts first. -/
def wordAct : List St → Stream → Stream
  | [],x => x
  | s::w,x => wordAct w (act s x)
def parity : List St → Bool
  | [] => false
  | s::w => xor (flip s) (parity w)
def dual : Bool → List St → List St
  | _,[] => []
  | b,s::w => next s b :: dual (emit s b) w
def rounds : Nat → List St → List St
  | 0,w => w
  | n+1,w => dual false (rounds n w)

theorem dual_length (b : Bool) (w : List St) : (dual b w).length=w.length := by
  induction w generalizing b with
  | nil => rfl
  | cons s w ih => simp [dual,ih]

theorem word_head (w : List St) (x : Stream) :
    wordAct w x 0=xor (x 0) (parity w) := by
  induction w generalizing x with
  | nil => simp [wordAct,parity]
  | cons s w ih =>
    rw [wordAct,ih]
    simp only [act,emit,parity]
    cases x 0 <;> cases flip s <;> cases parity w <;> rfl

theorem word_cons (w : List St) (b : Bool) (x : Stream) :
    wordAct w (cons b x)=cons (xor b (parity w)) (wordAct (dual b w) x) := by
  induction w generalizing b x with
  | nil => simp [wordAct,dual,parity]
  | cons s w ih =>
    rw [wordAct,act_cons,ih]
    simp only [dual,wordAct,parity,emit]
    congr 1
    cases b <;> cases flip s <;> cases parity w <;> rfl

theorem power_commute (s : St) (x : Stream) :
    ∀ n,power s (act s x) n=act s (power s x n)
  | 0 => rfl
  | n+1 => by rw [power,power_commute]; rfl

theorem word_replicate (s : St) (n : Nat) (x : Stream) :
    wordAct (List.replicate n s) x=power s x n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,wordAct,ih,power_commute]; rfl

theorem rounds_from (n : Nat) (w : List St) :
    rounds n (dual false w)=rounds (n+1) w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rounds,ih]; rfl

theorem word_zero_read (n : Nat) (w : List St) :
    wordAct w zero n=parity (rounds n w) := by
  induction n generalizing w with
  | zero => simpa [zero,rounds] using word_head w zero
  | succ n ih =>
    have z : zero=cons false zero := by funext k;cases k <;> rfl
    have h := congrFun (word_cons w false zero) (n+1)
    rw [←z] at h
    change wordAct w zero (n+1)=wordAct (dual false w) zero n at h
    rw [h,ih,rounds_from]

/-- Exact formula for every actual center cell after the initial black cell. -/
theorem center_dual (n : Nat) :
    Rule30Prize.center (n+1)=parity (rounds n (List.replicate (n+1) C)) := by
  rw [center_power,←word_replicate,word_zero_read]

/-- A useful exact recursion; it does not close the family of diagonal words. -/
theorem dual_two_C (w : List St) :
    dual false (dual false (C::w))=A::dual true (dual true w) := rfl

theorem dual_two_CC (w : List St) :
    dual false (dual false (C::C::w))=A::C::dual false (dual false w) := rfl

theorem dual_A_prefix (w : List St) : dual false (A::w)=A::dual false w := rfl

/-- All powers of A recur as their own sections along the all-zero ray. -/
theorem dual_A_power (b : Nat) : dual false (List.replicate b A)=List.replicate b A := by
  induction b with
  | zero => rfl
  | succ b ih => simp [List.replicate_succ,dual,next,emit,flip,ih]

theorem rounds_A_power (n b : Nat) : rounds n (List.replicate b A)=List.replicate b A := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rounds,ih,dual_A_power]

/-- These persistent sections are genuinely distinct functions, not just long words. -/
theorem A_powers_distinct (a b : Nat) (h : a<b) :
    wordAct (List.replicate a A) ≠ wordAct (List.replicate b A) := by
  intro eq
  have e := congrFun (congrFun eq seed) (2*b)
  rw [word_replicate,word_replicate,power_seed,power_seed] at e
  change cell a ((a:Int)-((2*b:Nat):Int))=cell b ((b:Int)-((2*b:Nat):Int)) at e
  rw [cell_eq_false_of_lt a _ (by omega),show (b:Int)-((2*b:Nat):Int)= -(b:Int) by omega,
    cell_left_edge] at e
  cases e

#print axioms SeedAutomaton.center_dual
#print axioms SeedAutomaton.A_powers_distinct
end SeedAutomaton
