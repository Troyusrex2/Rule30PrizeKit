module
public import WordBoundary
@[expose] public section
namespace TemporalAncestry
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration ReturnActions ReturnSections WordBoundary
open ReturnSections.State

theorem memory_A (p o : Bool) (h : memory p o=A) : p=false ∧ o=false := by
  cases p <;> cases o <;> simp_all [memory]
theorem memory_C (p o : Bool) (h : memory p o=C) : p=true := by
  cases p <;> cases o <;> simp_all [memory]

/-- A white adjacent pair cannot become a leading black cell for two
consecutive steps: the first rise also turns its older neighbor black. -/
theorem white_pair_rise_falls (x : Code) (j : Nat)
    (old : x j=false) (current : x (j+1)=false)
    (rise : T x (j+1)=true) : T (T x) (j+1)=false := by
  cases j with
  | zero => simp only [T,current,old] at rise;cases rise
  | succ j =>
    have older : x j=true := by
      simp only [T,current,old] at rise
      cases h:x j <;> simp_all
    have near : T x (j+1)=true := by
      cases j with
      | zero => simp only [T,old,older];rfl
      | succ j => simp only [T,old,older];rfl
    change xor (T x (j+2)) (T x (j+1)||T x j)=false
    rw [rise,near]
    rfl

/-- Universal temporal forbidden factor, independent of period, support,
or edge value. These are categorical boundary memory states. -/
theorem no_ACC (n : Nat) (x : Code)
    (a : stateAfter A x n=A) (c : stateAfter A (T x) n=C) :
    stateAfter A (T (T x)) n≠C := by
  cases n with
  | zero => intro h;cases h
  | succ n =>
    cases n with
    | zero =>
      simp only [stateAfter,next,T] at a c
      cases h:x 0 <;> simp_all
    | succ j =>
      rw [after_two] at a c ⊢
      obtain ⟨current,old⟩:=memory_A _ _ a
      have rise:=memory_C _ _ c
      have falls:=white_pair_rise_falls x j old current rise
      intro cc
      have black:=memory_C _ _ cc
      rw [falls] at black
      cases black

theorem no_ACC_from (n s : Nat) (x : Code)
    (a : stateAfter A (iter s x) n=A)
    (c : stateAfter A (iter (s+1) x) n=C) :
    stateAfter A (iter (s+2) x) n≠C := no_ACC n (iter s x) a c

theorem temporal_tail_two (n P : Nat) (x : Code) :
    temporalWord n x (P+2)=temporalWord n (iter 2 x) P ++
      [stateAfter A (iter 1 x) n,stateAfter A x n] := by
  induction P with
  | zero => rfl
  | succ P ih =>
    change stateAfter A (iter (P+2) x) n :: temporalWord n x (P+2)=
      (stateAfter A (iter P (iter 2 x)) n :: temporalWord n (iter 2 x) P) ++ _
    rw [←iter_add,show 2+P=P+2 by omega,ih]
    rfl

/-- A cyclic source word cannot begin A and end CC. In particular this
excludes every repeated power of the former AAACBCCC counterexample,
uniformly in prefix depth and period, without the P8 closure table. -/
theorem word_end_obstruction (n P : Nat) (x : Code)
    (fixed : AgreeBelow n (iter (P+3) x) x) (middle : List State)
    (equal : returnWord n (P+3) x=A::middle++[C,C]) : False := by
  rw [returnWord_eq,sections_temporal] at equal
  have head:=congrArg (fun w : List State => w.head?) equal
  change some (stateAfter A (iter (P+2) x) n)=some A at head
  have isA:=Option.some.inj head
  have tails:=equal
  rw [show P+3=(P+1)+2 by omega,temporal_tail_two] at tails
  have last:=congrArg (fun w : List State => w.reverse.head?) tails
  have prev:=congrArg (fun w : List State => w.reverse.tail.head?) tails
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.cons_append,List.head?_cons] at last
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.cons_append,List.tail_cons,List.head?_cons] at prev
  have firstC : stateAfter A x n=C := Option.some.inj last
  have nextC : stateAfter A (iter 1 x) n=C := Option.some.inj prev
  have atR : stateAfter A (iter ((P+2)+1) x) n=C :=
    (after_agree A _ _ n fixed).trans firstC
  have atR1 : stateAfter A (iter ((P+2)+2) x) n=C := by
    have preAgreement:=iter_agree fixed 1
    have state:=after_agree A _ _ n preAgreement
    rw [←iter_add] at state
    exact state.trans nextC
  exact no_ACC_from n (P+2) x isA atR atR1

def bad : List State := [A,A,A,C,B,C,C,C]
def badPower : Nat → List State
  | 0 => []
  | m+1 => badPower m++bad
def badMiddle : Nat → List State
  | 0 => [A,A,C,B,C]
  | m+1 => badMiddle m++[C,C,A,A,A,C,B,C]

theorem bad_shape (m : Nat) : badPower (m+1)=A::badMiddle m++[C,C] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change badPower (m+1)++bad=A::(badMiddle m++[C,C,A,A,A,C,B,C])++[C,C]
    rw [ih]
    simp only [bad,List.cons_append,List.append_assoc,List.nil_append]

theorem all_bad_powers_unreachable (n m : Nat) (x : Code)
    (fixed : AgreeBelow n (iter (8*(m+1)) x) x) :
    returnWord n (8*(m+1)) x≠badPower (m+1) := by
  intro eq
  have arithmetic : 8*(m+1)=(8*m+5)+3 := by omega
  rw [bad_shape,arithmetic] at eq
  rw [arithmetic] at fixed
  exact word_end_obstruction n (8*m+5) x fixed (badMiddle m) eq

end TemporalAncestry
