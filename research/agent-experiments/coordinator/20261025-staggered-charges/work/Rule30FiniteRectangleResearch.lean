module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
Four distinct finitely supported physical Rule30 starts can form a permanent
XOR rectangle. The difference of a paired seedPrefix stays in a two-cell strip
moving right at speed one, independently of its shared left tail. This
refutes a proposed strengthening of XOR rigidity to four finite histories;
it does not refute the canonical left-edge observer or solve Problem 1.
-/

@[expose] public section
namespace Rule30FiniteRectangleResearch
open Ruliology.CellularAutomata.Rule30Jen (rule)

def march (s : Nat → Bool) : Nat → Bool
  | 0 => s 0
  | 1 => xor (s 1) (s 0)
  | n+2 => xor (s (n+2)) (s (n+1) || s n)

def seedPrefix (b : Bool) (s : Nat → Bool) : Nat → Bool
  | 0 => b
  | 1 => true
  | 2 => false
  | n+3 => s n

def nextTail (s : Nat → Bool) (n : Nat) := march (march (seedPrefix false s)) (n+3)

theorem seedPrefix_true_succ (s : Nat → Bool) (n : Nat) :
    seedPrefix true s (n+1)=seedPrefix false s (n+1) := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

theorem march_true_ge3 (s : Nat → Bool) (n : Nat) :
    march (seedPrefix true s) (n+3)=march (seedPrefix false s) (n+3) := by
  change xor (seedPrefix true s (n+3))
    (seedPrefix true s (n+2) || seedPrefix true s (n+1))=_
  rw [seedPrefix_true_succ s (n+2),seedPrefix_true_succ s (n+1),seedPrefix_true_succ s n]
  rfl

theorem two_prefix (b : Bool) (s : Nat → Bool) :
    march (march (seedPrefix b s))=seedPrefix b (nextTail s) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => cases b <;> rfl
    | succ n =>
      cases n with
      | zero => cases b <;> rfl
      | succ n =>
        cases b with
        | false => rfl
        | true =>
          cases n with
          | zero => simp [march,seedPrefix,nextTail]
          | succ n =>
            cases n with
            | zero => simp [march,seedPrefix,nextTail]
            | succ n =>
              change xor (march (seedPrefix true s) (n+5))
                (march (seedPrefix true s) (n+4) || march (seedPrefix true s) (n+3))=_
              rw [march_true_ge3 s (n+2),march_true_ge3 s (n+1),march_true_ge3 s n]
              rfl

def evol (s : Nat → Bool) : Nat → Nat → Bool
  | 0 => s
  | t+1 => march (evol s t)

theorem evol_add (s : Nat → Bool) (t k : Nat) : evol s (t+k)=evol (evol s t) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change march (evol s (t+k))=march (evol (evol s t) k)
    exact congrArg march ih

def tailEvol (s : Nat → Bool) : Nat → Nat → Bool
  | 0 => s
  | k+1 => nextTail (tailEvol s k)

theorem even_shape (b : Bool) (s : Nat → Bool) (k : Nat) :
    evol (seedPrefix b s) (2*k)=seedPrefix b (tailEvol s k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2*(k+1)=2*k+2 by omega,evol_add,ih]
    exact two_prefix b (tailEvol s k)

theorem odd_shape (b : Bool) (s : Nat → Bool) (k : Nat) :
    evol (seedPrefix b s) (2*k+1)=march (seedPrefix b (tailEvol s k)) := by
  rw [evol,even_shape]

theorem pair_difference_independent_tail (s r : Nat → Bool) (t n : Nat) :
    xor (evol (seedPrefix false s) t n) (evol (seedPrefix true s) t n)=
    xor (evol (seedPrefix false r) t n) (evol (seedPrefix true r) t n) := by
  obtain ⟨k,rfl|rfl⟩ : ∃ k, t=2*k ∨ t=2*k+1 := ⟨t/2,by omega⟩
  · rw [even_shape,even_shape,even_shape,even_shape]
    cases n with
    | zero => rfl
    | succ n => simp only [seedPrefix_true_succ,Bool.xor_self]
  · rw [odd_shape,odd_shape,odd_shape,odd_shape]
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => simp [march,seedPrefix]
        | succ n =>
          change xor (march (seedPrefix false (tailEvol s k)) (n+3))
            (march (seedPrefix true (tailEvol s k)) (n+3))=_
          rw [march_true_ge3,march_true_ge3]
          simp only [Bool.xor_self]

def wall (s : Nat → Bool) (n : Int) : Bool := if 0≤n then s n.toNat else false

theorem wall_march (s : Nat → Bool) (n : Int) :
    wall (march s) n=rule (wall s n) (wall s (n-1)) (wall s (n-2)) := by
  by_cases hn : 0≤n
  · have he : n=(n.toNat : Int) := by omega
    rw [he]
    generalize n.toNat=k
    cases k with
    | zero => simp [wall,march,rule]
    | succ k =>
      cases k with
      | zero => simp [wall,march,rule]
      | succ k =>
        simp only [wall,show (0:Int)≤((k+1+1:Nat):Int) by omega,
          show (0:Int)≤((k+1+1:Nat):Int)-1 by omega,
          show (0:Int)≤((k+1+1:Nat):Int)-2 by omega,ite_true,
          show (((k+1+1:Nat):Int)-1).toNat=k+1 by omega,
          show (((k+1+1:Nat):Int)-2).toNat=k by omega,Int.toNat_natCast,march,rule]
  · simp only [wall,hn,show ¬(0:Int)≤n-1 by omega,
      show ¬(0:Int)≤n-2 by omega,ite_false,rule]
    rfl

/-- Physical coordinates: right boundary at position t, index n points left. -/
def physical (s : Nat → Bool) (t : Nat) (p : Int) := wall (evol s t) ((t:Int)-p)

theorem physical_step (s : Nat → Bool) (t : Nat) (p : Int) :
    physical s (t+1) p=rule (physical s t (p-1)) (physical s t p)
      (physical s t (p+1)) := by
  unfold physical
  rw [evol,wall_march]
  congr 1 <;> congr 1 <;> omega

def finiteStart (b c : Bool) := seedPrefix b (fun n=>if n=0 then c else false)

theorem initial_support (b c : Bool) (p : Int) (hp : p < -3 ∨ 0 < p) :
    physical (finiteStart b c) 0 p=false := by
  rcases hp with hp|hp
  · have hn : 3<(-p).toNat := by omega
    obtain ⟨k,hk⟩ : ∃ k, (-p).toNat=k+4 := ⟨(-p).toNat-4,by omega⟩
    simp [physical,evol,wall,finiteStart,seedPrefix,show (0:Int)≤-p by omega,hk]
  · unfold physical wall
    split
    · rename_i h
      omega
    · rfl

theorem initial_distinct (b c b' c' : Bool)
    (h : physical (finiteStart b c) 0=physical (finiteStart b' c') 0) :
    b=b' ∧ c=c' := by
  constructor
  · have hh:=congrFun h 0
    simpa [physical,evol,wall,finiteStart,seedPrefix] using hh
  · have hh:=congrFun h (-3)
    simpa [physical,evol,wall,finiteStart,seedPrefix] using hh

/-- Four distinct finite physical starts, not four auxiliary linear modes. -/
theorem finite_rectangle (c d : Bool) (t : Nat) (p : Int) :
    xor (physical (finiteStart false c) t p) (physical (finiteStart true c) t p)=
    xor (physical (finiteStart false d) t p) (physical (finiteStart true d) t p) := by
  unfold physical wall finiteStart
  split
  · exact pair_difference_independent_tail _ _ _ _
  · rfl

end Rule30FiniteRectangleResearch
