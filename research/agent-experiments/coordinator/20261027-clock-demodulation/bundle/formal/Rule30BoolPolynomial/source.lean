module
public import Ruliology.CellularAutomata.Rule30Prize

/-! Small Boolean-polynomial normalization with an explicit evaluation proof.
The lists hold square-free monomial bit masks, with XOR coefficients.
Closed coefficient checks use the kernel; no truth-table semantics is assumed. -/
@[expose] public section
namespace Rule30BoolPolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev Poly := List Nat

def mon (n mask : Nat) (x : Nat → Bool) : Bool :=
  match n with
  | 0 => true
  | n+1 => (if mask.testBit n then x n else true) && mon n mask x

def eval (n : Nat) (p : Poly) (x : Nat → Bool) : Bool :=
  match p with
  | [] => false
  | m::ms => xor (mon n m x) (eval n ms x)

def insert (m : Nat) : Poly → Poly
  | [] => [m]
  | a::as => if m=a then as else if m<a then m::a::as else a::insert m as

def add : Poly → Poly → Poly
  | [],q => q
  | m::ms,q => insert m (add ms q)

def scale (m : Nat) : Poly → Poly
  | [] => []
  | a::as => insert (m ||| a) (scale m as)

def mul : Poly → Poly → Poly
  | [],_ => []
  | m::ms,q => add (scale m q) (mul ms q)

def one : Poly := [0]
def var (j : Nat) : Poly := [2^j]
def neg (p : Poly) : Poly := add one p
def bor (p q : Poly) : Poly := add (add p q) (mul p q)

theorem xor_cancel (a b : Bool) : xor a (xor a b)=b := by
  cases a <;> cases b <;> rfl

theorem gate_join (a b x u v : Bool) :
    ((if a || b then x else true) && (u && v)) =
    (((if a then x else true) && u) && ((if b then x else true) && v)) := by
  cases a <;> cases b <;> cases x <;> simp

theorem mon_or (n a b : Nat) (x : Nat → Bool) :
    mon n (a ||| b) x = (mon n a x && mon n b x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mon,Nat.testBit_or,ih]
    exact gate_join _ _ _ _ _

theorem mon_zero (n : Nat) (x : Nat → Bool) : mon n 0 x=true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [mon,ih]

theorem eval_insert (n m : Nat) (p : Poly) (x : Nat → Bool) :
    eval n (insert m p) x=xor (mon n m x) (eval n p x) := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    simp only [insert]
    split
    · rename_i h
      subst a
      exact (xor_cancel _ _).symm
    · split
      · rfl
      · simp only [eval,ih]
        exact Bool.xor_left_comm _ _ _

theorem eval_add (n : Nat) (p q : Poly) (x : Nat → Bool) :
    eval n (add p q) x=xor (eval n p x) (eval n q x) := by
  induction p with
  | nil => simp [add,eval]
  | cons m ms ih =>
    rw [add,eval_insert,ih]
    exact (Bool.xor_assoc _ _ _).symm

theorem eval_scale (n m : Nat) (p : Poly) (x : Nat → Bool) :
    eval n (scale m p) x=(mon n m x && eval n p x) := by
  induction p with
  | nil => simp [scale,eval]
  | cons a as ih =>
    rw [scale,eval_insert,mon_or,ih]
    exact (Bool.and_xor_distrib_left _ _ _).symm

theorem eval_mul (n : Nat) (p q : Poly) (x : Nat → Bool) :
    eval n (mul p q) x=(eval n p x && eval n q x) := by
  induction p with
  | nil => simp [mul,eval]
  | cons m ms ih =>
    rw [mul,eval_add,eval_scale,ih]
    exact (Bool.and_xor_distrib_right _ _ _).symm

theorem eval_one (n : Nat) (x : Nat → Bool) : eval n one x=true := by
  simp [one,eval,mon_zero]

theorem eval_neg (n : Nat) (p : Poly) (x : Nat → Bool) :
    eval n (neg p) x=!(eval n p x) := by
  rw [neg,eval_add,eval_one]
  exact Bool.true_xor _

theorem or_poly (a b : Bool) : xor (xor a b) (a && b)=(a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_bor (n : Nat) (p q : Poly) (x : Nat → Bool) :
    eval n (bor p q) x=(eval n p x || eval n q x) := by
  rw [bor,eval_add,eval_add,eval_mul]
  exact or_poly _ _

end Rule30BoolPolynomial
