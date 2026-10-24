module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# The moving-frame diagonal and a limitation of orbit-period arguments

The packed Rule 30 row is exact, but the center reads an increasing bit index.
A binary counter has unbounded exact periods at every fixed bit index while
its corresponding diagonal is eventually white. Thus those period facts alone
do not prove the Rule 30 center result. No novelty or prize solution is claimed.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30MovingFrameBarrierResearch

open Rule30Jen Rule30Prize

def step (a : Nat) : Nat := a ^^^ ((a <<< 1) ||| (a <<< 2))

def rows : Nat → Nat
  | 0 => 1
  | t+1 => step (rows t)

def readAt (a : Nat) (p : Int) : Bool := if p<0 then false else a.testBit p.toNat

theorem step_bit (a k : Nat) :
    (step a).testBit k=xor (a.testBit k)
      ((if 1≤k then a.testBit (k-1) else false) ||
       (if 2≤k then a.testBit (k-2) else false)) := by
  simp [step,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft]

theorem at_step (a : Nat) (p : Int) :
    readAt (step a) p=rule (readAt a p) (readAt a (p-1)) (readAt a (p-2)) := by
  by_cases hp : p<0
  · simp [readAt,hp,show p-1<0 by omega,show p-2<0 by omega,rule]
  · obtain ⟨k,rfl⟩ : ∃ k : Nat, (k:Int)=p := ⟨p.toNat,by omega⟩
    rw [readAt,ite_eq_right (by omega),Int.toNat_natCast,step_bit]
    simp only [readAt,rule]
    by_cases h1 : 1≤k
    · by_cases h2 : 2≤k
      · simp only [ite_eq_left h1,ite_eq_left h2,ite_eq_right (show ¬(k:Int)-2<0 by omega),
          ite_eq_right (show ¬(k:Int)-1<0 by omega),ite_eq_right (show ¬(k:Int)<0 by omega),
          show ((k:Int)-2).toNat=k-2 by omega,
          show ((k:Int)-1).toNat=k-1 by omega,Int.toNat_natCast]
      · have : k=1 := by omega
        subst k
        simp
    · have : k=0 := by omega
      subst k
      simp

/-- Zero outside the right light cone. -/
theorem right_white : ∀ (t : Nat) (p : Int), (t:Int)<p → cell t p=false
  | 0,p,hp => by simp [cell,show p≠0 by omega]
  | t+1,p,hp => by
      rw [cell,right_white t (p-1) (by omega),right_white t p (by omega),
        right_white t (p+1) (by omega)]
      rfl

/-- Indices count from the moving RIGHT edge. -/
theorem rows_sound (t : Nat) (p : Int) : readAt (rows t) p=cell t (t-p) := by
  induction t generalizing p with
  | zero =>
      by_cases hp : p<0
      · simp [readAt,hp,cell,show p≠0 by omega]
      · simp only [rows,readAt,ite_eq_right hp,cell,Int.ofNat_zero]
        change (Bool.toNat true).testBit p.toNat=decide (0-p=0)
        rw [Nat.testBit_bool_toNat]
        simp [show p.toNat=0 ↔ p=0 by omega]
  | succ t ih =>
      by_cases hp : p<0
      · rw [readAt,ite_eq_left hp,right_white _ _ (by omega)]
      · rw [rows,at_step,ih,ih,ih,cell]
        congr 1 <;> congr 1 <;> omega

/-- The bit index grows with time. Fixed-index period facts do not address it. -/
theorem center_is_diagonal (t : Nat) : center t=(rows t).testBit t := by
  have h := rows_sound t t
  simpa [readAt,center,show ¬(t:Int)<0 by omega] using h.symm

def counterBit (k t : Nat) : Bool := (t+1).testBit k
def counterDiagonal (t : Nat) : Bool := counterBit t t

theorem counterBit_period (k t : Nat) :
    counterBit k (t+2^(k+1))=counterBit k t := by
  unfold counterBit
  rw [show t+2^(k+1)+1=2^(k+1)+(t+1) by omega]
  exact Nat.testBit_two_pow_add_gt (by omega) _

theorem counterBit_no_short_period (k P : Nat) (hP : 0<P) (hsmall : P<2^(k+1)) :
    ¬∀ t, counterBit k (t+P)=counterBit k t := by
  intro h
  by_cases hp : P<2^k
  · let t := 2^k-P-1
    have hlow : t+1<2^k := by dsimp [t]; omega
    have heq : t+P+1=2^k := by dsimp [t]; omega
    have hh := h t
    unfold counterBit at hh
    rw [heq,Nat.testBit_two_pow_self,Nat.testBit_lt_two_pow hlow] at hh
    contradiction
  · have hbit : P.testBit k=true :=
      Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) hsmall
    have hh := h (2^(k+1)-1)
    have heq : 2^(k+1)-1+P=(P-1)+2^(k+1) := by
      have := Nat.two_pow_pos (k+1)
      omega
    rw [heq,counterBit_period] at hh
    unfold counterBit at hh
    rw [show P-1+1=P by omega,show 2^(k+1)-1+1=2^(k+1) by have := Nat.two_pow_pos (k+1); omega,
      hbit,Nat.testBit_two_pow] at hh
    simp at hh

theorem counterBit_exact_period (k : Nat) :
    (∀ t, counterBit k (t+2^(k+1))=counterBit k t) ∧
    ∀ P, 0<P → (∀ t, counterBit k (t+P)=counterBit k t) → 2^(k+1)≤P := by
  refine ⟨counterBit_period k,?_⟩
  intro P hP hh
  by_cases hp : 2^(k+1)≤P
  · exact hp
  · exact False.elim (counterBit_no_short_period k P hP (by omega) hh)

theorem counterBit_periods_unbounded (B : Nat) :
    ∃ k, ∀ P, 0<P → (∀ t, counterBit k (t+P)=counterBit k t) → B<P := by
  refine ⟨B,fun P hP hh => ?_⟩
  have hl := (counterBit_exact_period B).2 P hP hh
  have hg : B+1<2^(B+1) := Nat.lt_two_pow_self
  omega

theorem counterDiagonal_white (t : Nat) (ht : 2≤t) : counterDiagonal t=false := by
  apply Nat.testBit_lt_two_pow
  have h : ∀ n, n+3<2^(n+2) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
        rw [show n+1+2=(n+2)+1 by omega,Nat.pow_succ (n:=2)]
        omega
  have hh := h (t-2)
  simpa [show t-2+2=t by omega,show t-2+3=t+1 by omega] using hh

theorem counterDiagonal_eventuallyPeriodic : EventuallyPeriodic counterDiagonal :=
  eventuallyPeriodic_of_const (T:=2) (fun t ht => counterDiagonal_white t ht)

/-- Preserve the low edge bit, just as the Rule 30 packed orbit does. -/
def oddCounterBit (k t : Nat) : Bool := (2*t+1).testBit k

theorem oddCounterBit_zero (t : Nat) : oddCounterBit 0 t=true := by
  simp [oddCounterBit]

theorem oddCounterBit_succ (k t : Nat) : oddCounterBit (k+1) t=t.testBit k := by
  unfold oddCounterBit
  rw [Nat.testBit_succ]
  congr 1
  omega

theorem oddCounterBit_exact_period (k : Nat) :
    (∀ t, oddCounterBit (k+1) (t+2^(k+1))=oddCounterBit (k+1) t) ∧
    ∀ P, 0<P → (∀ t, oddCounterBit (k+1) (t+P)=oddCounterBit (k+1) t) → 2^(k+1)≤P := by
  constructor
  · intro t
    rw [oddCounterBit_succ,oddCounterBit_succ,Nat.add_comm]
    exact Nat.testBit_two_pow_add_gt (by omega) _
  · intro P hP hh
    apply (counterBit_exact_period k).2 P hP
    intro t
    have h := hh (t+1)
    simpa only [oddCounterBit_succ,show t+1+P=t+P+1 by omega,counterBit] using h

theorem oddCounterDiagonal_white (t : Nat) (ht : 3≤t) : oddCounterBit t t=false := by
  apply Nat.testBit_lt_two_pow
  have h : ∀ n, 2*(n+3)+1<2^(n+3) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
        rw [show n+1+3=(n+3)+1 by omega,Nat.two_pow_succ]
        omega
  have hh := h (t-3)
  simpa only [show t-3+3=t by omega] using hh

theorem global_period_of_eventual_period {f : Nat → Bool} {M T P : Nat}
    (hM : 0<M) (hm : ∀ t, f (t+M)=f t)
    (hp : ∀ t, T≤t → f (t+P)=f t) : ∀ t, f (t+P)=f t := by
  have hmul := Rule30Jen.periodic_mul (T:=0) (P:=M) (fun t _ => hm t)
  have hbig : T≤T*M := by
    have h := Nat.mul_le_mul_left T (show 1≤M by omega)
    simpa using h
  intro t
  calc f (t+P)=f (t+P+T*M) := (hmul T (t+P) (by omega)).symm
    _=f (t+T*M) := by rw [show t+P+T*M=(t+T*M)+P by omega]; exact hp _ (by omega)
    _=f t := hmul T t (by omega)

theorem oddCounterBit_eventual_period_lower_bound (k T P : Nat) (hP : 0<P)
    (hh : ∀ t, T≤t → oddCounterBit (k+1) (t+P)=oddCounterBit (k+1) t) : 2^(k+1)≤P :=
  (oddCounterBit_exact_period k).2 P hP
    (global_period_of_eventual_period (Nat.two_pow_pos _) (oddCounterBit_exact_period k).1 hh)

/-- A countermodel to the inference from fixed-edge periods alone, even with
the low edge bit permanently black and with arbitrary transients allowed. -/
theorem countermodel : ∃ F : Nat → Nat → Bool,
    (∀ t, F 0 t=true) ∧
    (∀ k, ∃ P, 0<P ∧ ∀ t, F (k+1) (t+P)=F (k+1) t) ∧
    (∀ B, ∃ k, ∀ T P, 0<P → (∀ t, T≤t → F k (t+P)=F k t) → B<P) ∧
    (∃ T, ∀ t, T≤t → F t t=false) := by
  refine ⟨oddCounterBit,oddCounterBit_zero,?_,?_,3,oddCounterDiagonal_white⟩
  · intro k
    exact ⟨2^(k+1),Nat.two_pow_pos _,(oddCounterBit_exact_period k).1⟩
  · intro B
    refine ⟨B+1,fun T P hP hh => ?_⟩
    have hl := oddCounterBit_eventual_period_lower_bound B T P hP hh
    have hg : B+1<2^(B+1) := Nat.lt_two_pow_self
    omega

end Ruliology.CellularAutomata.Rule30MovingFrameBarrierResearch
