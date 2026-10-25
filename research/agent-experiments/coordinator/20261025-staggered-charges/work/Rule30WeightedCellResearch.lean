module

public import Init.Data.Fin.Lemmas
public import Ruliology.CellularAutomata.Rule30Prize

/-!
Sixteen translated two-pulse tests force any arbitrary-position, one-cell
paired parity score after four Rule30 updates to be state-independent. Old
and new scores may differ, so there is no spatial or temporal clock bound.
This is an obstruction for one-cell charges, not an all-width staggered
classification and not a solution of the Rule30 prize problem.
-/

@[expose] public section
namespace Rule30WeightedCellResearch

theorem sub_eq_zero : ∀ {a b : Fin 2}, a-b=0 ↔ a=b := by decide +kernel
theorem sub_right_inj : ∀ {a b c : Fin 2}, a-b=a-c ↔ b=c := by decide +kernel
@[simp] theorem p_add_sub_cancel : ∀ a b : Fin 2, a+b-b=a := by decide +kernel
@[simp] theorem p_zero_add : ∀ a : Fin 2, 0+a=a := by decide +kernel
@[simp] theorem p_add_zero : ∀ a : Fin 2, a+0=a := by decide +kernel
@[simp] theorem p_sub_zero : ∀ a : Fin 2, a-0=a := by decide +kernel
@[simp] theorem p_sub_self : ∀ a : Fin 2, a-a=0 := by decide +kernel
theorem p_sub_as_add : ∀ a b : Fin 2, a-b=a+b := by decide +kernel
theorem p_add_assoc : ∀ a b c : Fin 2, (a+b)+c=a+(b+c) := by decide +kernel
theorem p_add_comm : ∀ a b : Fin 2, a+b=b+a := by decide +kernel
theorem p_add_left_comm : ∀ a b c : Fin 2, a+(b+c)=b+(a+c) := by decide +kernel
theorem p_cancel_pair : ∀ a b : Fin 2, a+(a+b)=b := by decide +kernel
theorem p_add_self : ∀ a : Fin 2, a+a=0 := by decide +kernel

macro "weighted_parity_nf" : tactic => `(tactic|
  simp only [p_sub_as_add,p_add_assoc,p_add_comm,p_add_left_comm,p_cancel_pair,
    p_add_self,p_add_zero,p_zero_add])


def shrink : List Bool → List Bool
  | a::b::c::xs => Ruliology.CellularAutomata.Rule30Jen.rule a b c :: shrink (b::c::xs)
  | _ => []
def four (xs : List Bool) := shrink (shrink (shrink (shrink xs)))
def input (a : Fin 4) : List Bool := (List.range 24).map fun p =>
  (a.val.testBit 0 && decide (p=8)) || (a.val.testBit 1 && decide (p=15))
def crop (xs : List Bool) := (xs.drop 4).take 16
def beforeRows : List (List Bool) := [[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false],[false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false],[false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false],[false,false,false,false,true,false,false,false,false,false,false,true,false,false,false,false]]
def afterRows : List (List Bool) := [[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false],[true,true,false,false,true,false,false,false,true,false,false,false,false,false,false,false],[false,false,false,false,false,false,false,true,true,false,false,true,false,false,false,true],[true,true,false,false,true,false,false,false,false,false,false,true,false,false,false,true]]
def before (a : Fin 4) := beforeRows.getD a.val []
def after (a : Fin 4) := afterRows.getD a.val []
theorem before_correct : ∀ a : Fin 4, crop (input a)=before a := by decide +kernel
theorem after_correct : ∀ a : Fin 4, four (input a)=after a := by decide +kernel

def chargeAux (h : Nat → Bool → Bool → Fin 2) : Nat → List Bool → List Bool → Fin 2
  | i,a::as,b::bs => (h i a b-h i false false)+chargeAux h (i+1) as bs
  | _,_,_ => 0
def charge (h : Nat → Bool → Bool → Fin 2) (a b : List Bool) := chargeAux h 0 a b
def selector (b : Bool) : Fin 4 := if b then 2 else 0
def mixedBefore (h : Nat → Bool → Bool → Fin 2) (b : Bool) :=
  charge h (before 0) (before (selector b))+
  charge h (before 1) (before (selector b))+
  charge h (before 2) (before (selector b))+
  charge h (before 3) (before (selector b))
def mixedAfter (h : Nat → Bool → Bool → Fin 2) (b : Bool) :=
  charge h (after 0) (after (selector b))+
  charge h (after 1) (after (selector b))+
  charge h (after 2) (after (selector b))+
  charge h (after 3) (after (selector b))


def add4 (a b c d : Fin 2) := a+b+c+d

theorem add4_add : ∀ a b c d e f g h : Fin 2,
    add4 (a+e) (b+f) (c+g) (d+h)=add4 a b c d+add4 e f g h := by decide +kernel

def mixedAux (h : Nat → Bool → Bool → Fin 2) :
    Nat → List Bool → List Bool → List Bool → List Bool → List Bool → Fin 2
  | i,a::as,b::bs,c::cs,d::ds,e::es =>
    add4 (h i a e-h i false false) (h i b e-h i false false)
      (h i c e-h i false false) (h i d e-h i false false)+
    mixedAux h (i+1) as bs cs ds es
  | i,a,b,c,d,e => add4 (chargeAux h i a e) (chargeAux h i b e)
      (chargeAux h i c e) (chargeAux h i d e)

theorem mixedAux_eq (h : Nat → Bool → Bool → Fin 2) (i : Nat)
    (a b c d e : List Bool) :
    mixedAux h i a b c d e=add4 (chargeAux h i a e) (chargeAux h i b e)
      (chargeAux h i c e) (chargeAux h i d e) := by
  induction a generalizing i b c d e with
  | nil => rfl
  | cons a as ih =>
    cases b <;> cases c <;> cases d <;> cases e <;>
      simp only [mixedAux,chargeAux,ih,add4_add]

theorem mixed_before_zero (h : Nat → Bool → Bool → Fin 2) (b : Bool) :
    mixedBefore h b=0 := by
  unfold mixedBefore charge
  change add4 _ _ _ _=_
  rw [←mixedAux_eq]
  cases b with
  | false =>
    change (((h 0 false false-h 0 false false)+(h 0 false false-h 0 false false)+(h 0 false false-h 0 false false)+(h 0 false false-h 0 false false))+(((h 1 false false-h 1 false false)+(h 1 false false-h 1 false false)+(h 1 false false-h 1 false false)+(h 1 false false-h 1 false false))+(((h 2 false false-h 2 false false)+(h 2 false false-h 2 false false)+(h 2 false false-h 2 false false)+(h 2 false false-h 2 false false))+(((h 3 false false-h 3 false false)+(h 3 false false-h 3 false false)+(h 3 false false-h 3 false false)+(h 3 false false-h 3 false false))+(((h 4 false false-h 4 false false)+(h 4 true false-h 4 false false)+(h 4 false false-h 4 false false)+(h 4 true false-h 4 false false))+(((h 5 false false-h 5 false false)+(h 5 false false-h 5 false false)+(h 5 false false-h 5 false false)+(h 5 false false-h 5 false false))+(((h 6 false false-h 6 false false)+(h 6 false false-h 6 false false)+(h 6 false false-h 6 false false)+(h 6 false false-h 6 false false))+(((h 7 false false-h 7 false false)+(h 7 false false-h 7 false false)+(h 7 false false-h 7 false false)+(h 7 false false-h 7 false false))+(((h 8 false false-h 8 false false)+(h 8 false false-h 8 false false)+(h 8 false false-h 8 false false)+(h 8 false false-h 8 false false))+(((h 9 false false-h 9 false false)+(h 9 false false-h 9 false false)+(h 9 false false-h 9 false false)+(h 9 false false-h 9 false false))+(((h 10 false false-h 10 false false)+(h 10 false false-h 10 false false)+(h 10 false false-h 10 false false)+(h 10 false false-h 10 false false))+(((h 11 false false-h 11 false false)+(h 11 false false-h 11 false false)+(h 11 true false-h 11 false false)+(h 11 true false-h 11 false false))+(((h 12 false false-h 12 false false)+(h 12 false false-h 12 false false)+(h 12 false false-h 12 false false)+(h 12 false false-h 12 false false))+(((h 13 false false-h 13 false false)+(h 13 false false-h 13 false false)+(h 13 false false-h 13 false false)+(h 13 false false-h 13 false false))+(((h 14 false false-h 14 false false)+(h 14 false false-h 14 false false)+(h 14 false false-h 14 false false)+(h 14 false false-h 14 false false))+(((h 15 false false-h 15 false false)+(h 15 false false-h 15 false false)+(h 15 false false-h 15 false false)+(h 15 false false-h 15 false false))+0))))))))))))))))=0
    weighted_parity_nf
  | true =>
    change (((h 0 false false-h 0 false false)+(h 0 false false-h 0 false false)+(h 0 false false-h 0 false false)+(h 0 false false-h 0 false false))+(((h 1 false false-h 1 false false)+(h 1 false false-h 1 false false)+(h 1 false false-h 1 false false)+(h 1 false false-h 1 false false))+(((h 2 false false-h 2 false false)+(h 2 false false-h 2 false false)+(h 2 false false-h 2 false false)+(h 2 false false-h 2 false false))+(((h 3 false false-h 3 false false)+(h 3 false false-h 3 false false)+(h 3 false false-h 3 false false)+(h 3 false false-h 3 false false))+(((h 4 false false-h 4 false false)+(h 4 true false-h 4 false false)+(h 4 false false-h 4 false false)+(h 4 true false-h 4 false false))+(((h 5 false false-h 5 false false)+(h 5 false false-h 5 false false)+(h 5 false false-h 5 false false)+(h 5 false false-h 5 false false))+(((h 6 false false-h 6 false false)+(h 6 false false-h 6 false false)+(h 6 false false-h 6 false false)+(h 6 false false-h 6 false false))+(((h 7 false false-h 7 false false)+(h 7 false false-h 7 false false)+(h 7 false false-h 7 false false)+(h 7 false false-h 7 false false))+(((h 8 false false-h 8 false false)+(h 8 false false-h 8 false false)+(h 8 false false-h 8 false false)+(h 8 false false-h 8 false false))+(((h 9 false false-h 9 false false)+(h 9 false false-h 9 false false)+(h 9 false false-h 9 false false)+(h 9 false false-h 9 false false))+(((h 10 false false-h 10 false false)+(h 10 false false-h 10 false false)+(h 10 false false-h 10 false false)+(h 10 false false-h 10 false false))+(((h 11 false true-h 11 false false)+(h 11 false true-h 11 false false)+(h 11 true true-h 11 false false)+(h 11 true true-h 11 false false))+(((h 12 false false-h 12 false false)+(h 12 false false-h 12 false false)+(h 12 false false-h 12 false false)+(h 12 false false-h 12 false false))+(((h 13 false false-h 13 false false)+(h 13 false false-h 13 false false)+(h 13 false false-h 13 false false)+(h 13 false false-h 13 false false))+(((h 14 false false-h 14 false false)+(h 14 false false-h 14 false false)+(h 14 false false-h 14 false false)+(h 14 false false-h 14 false false))+(((h 15 false false-h 15 false false)+(h 15 false false-h 15 false false)+(h 15 false false-h 15 false false)+(h 15 false false-h 15 false false))+0))))))))))))))))=0
    weighted_parity_nf

theorem mixed_after_local (h : Nat → Bool → Bool → Fin 2) (b : Bool) :
    mixedAfter h b=h 7 false b+h 7 true b := by
  unfold mixedAfter charge
  change add4 _ _ _ _=_
  rw [←mixedAux_eq]
  cases b with
  | false =>
    change (((h 0 false false-h 0 false false)+(h 0 true false-h 0 false false)+(h 0 false false-h 0 false false)+(h 0 true false-h 0 false false))+(((h 1 false false-h 1 false false)+(h 1 true false-h 1 false false)+(h 1 false false-h 1 false false)+(h 1 true false-h 1 false false))+(((h 2 false false-h 2 false false)+(h 2 false false-h 2 false false)+(h 2 false false-h 2 false false)+(h 2 false false-h 2 false false))+(((h 3 false false-h 3 false false)+(h 3 false false-h 3 false false)+(h 3 false false-h 3 false false)+(h 3 false false-h 3 false false))+(((h 4 false false-h 4 false false)+(h 4 true false-h 4 false false)+(h 4 false false-h 4 false false)+(h 4 true false-h 4 false false))+(((h 5 false false-h 5 false false)+(h 5 false false-h 5 false false)+(h 5 false false-h 5 false false)+(h 5 false false-h 5 false false))+(((h 6 false false-h 6 false false)+(h 6 false false-h 6 false false)+(h 6 false false-h 6 false false)+(h 6 false false-h 6 false false))+(((h 7 false false-h 7 false false)+(h 7 false false-h 7 false false)+(h 7 true false-h 7 false false)+(h 7 false false-h 7 false false))+(((h 8 false false-h 8 false false)+(h 8 true false-h 8 false false)+(h 8 true false-h 8 false false)+(h 8 false false-h 8 false false))+(((h 9 false false-h 9 false false)+(h 9 false false-h 9 false false)+(h 9 false false-h 9 false false)+(h 9 false false-h 9 false false))+(((h 10 false false-h 10 false false)+(h 10 false false-h 10 false false)+(h 10 false false-h 10 false false)+(h 10 false false-h 10 false false))+(((h 11 false false-h 11 false false)+(h 11 false false-h 11 false false)+(h 11 true false-h 11 false false)+(h 11 true false-h 11 false false))+(((h 12 false false-h 12 false false)+(h 12 false false-h 12 false false)+(h 12 false false-h 12 false false)+(h 12 false false-h 12 false false))+(((h 13 false false-h 13 false false)+(h 13 false false-h 13 false false)+(h 13 false false-h 13 false false)+(h 13 false false-h 13 false false))+(((h 14 false false-h 14 false false)+(h 14 false false-h 14 false false)+(h 14 false false-h 14 false false)+(h 14 false false-h 14 false false))+(((h 15 false false-h 15 false false)+(h 15 false false-h 15 false false)+(h 15 true false-h 15 false false)+(h 15 true false-h 15 false false))+0))))))))))))))))=h 7 false false+h 7 true false
    weighted_parity_nf
  | true =>
    change (((h 0 false false-h 0 false false)+(h 0 true false-h 0 false false)+(h 0 false false-h 0 false false)+(h 0 true false-h 0 false false))+(((h 1 false false-h 1 false false)+(h 1 true false-h 1 false false)+(h 1 false false-h 1 false false)+(h 1 true false-h 1 false false))+(((h 2 false false-h 2 false false)+(h 2 false false-h 2 false false)+(h 2 false false-h 2 false false)+(h 2 false false-h 2 false false))+(((h 3 false false-h 3 false false)+(h 3 false false-h 3 false false)+(h 3 false false-h 3 false false)+(h 3 false false-h 3 false false))+(((h 4 false false-h 4 false false)+(h 4 true false-h 4 false false)+(h 4 false false-h 4 false false)+(h 4 true false-h 4 false false))+(((h 5 false false-h 5 false false)+(h 5 false false-h 5 false false)+(h 5 false false-h 5 false false)+(h 5 false false-h 5 false false))+(((h 6 false false-h 6 false false)+(h 6 false false-h 6 false false)+(h 6 false false-h 6 false false)+(h 6 false false-h 6 false false))+(((h 7 false true-h 7 false false)+(h 7 false true-h 7 false false)+(h 7 true true-h 7 false false)+(h 7 false true-h 7 false false))+(((h 8 false true-h 8 false false)+(h 8 true true-h 8 false false)+(h 8 true true-h 8 false false)+(h 8 false true-h 8 false false))+(((h 9 false false-h 9 false false)+(h 9 false false-h 9 false false)+(h 9 false false-h 9 false false)+(h 9 false false-h 9 false false))+(((h 10 false false-h 10 false false)+(h 10 false false-h 10 false false)+(h 10 false false-h 10 false false)+(h 10 false false-h 10 false false))+(((h 11 false true-h 11 false false)+(h 11 false true-h 11 false false)+(h 11 true true-h 11 false false)+(h 11 true true-h 11 false false))+(((h 12 false false-h 12 false false)+(h 12 false false-h 12 false false)+(h 12 false false-h 12 false false)+(h 12 false false-h 12 false false))+(((h 13 false false-h 13 false false)+(h 13 false false-h 13 false false)+(h 13 false false-h 13 false false)+(h 13 false false-h 13 false false))+(((h 14 false false-h 14 false false)+(h 14 false false-h 14 false false)+(h 14 false false-h 14 false false)+(h 14 false false-h 14 false false))+(((h 15 false true-h 15 false false)+(h 15 false true-h 15 false false)+(h 15 true true-h 15 false false)+(h 15 true true-h 15 false false))+0))))))))))))))))=h 7 false true+h 7 true true
    weighted_parity_nf

def TestConserved (old new : Nat → Bool → Bool → Fin 2) : Prop :=
  ∀ a b : Fin 4, charge new (four (input a)) (four (input b))=
    charge old (crop (input a)) (crop (input b))

theorem first_coordinate (old new : Nat → Bool → Bool → Fin 2)
    (hc : TestConserved old new) (b : Bool) : new 7 false b=new 7 true b := by
  have h0:=hc 0 (selector b)
  have h1:=hc 1 (selector b)
  have h2:=hc 2 (selector b)
  have h3:=hc 3 (selector b)
  simp only [after_correct,before_correct] at h0 h1 h2 h3
  have hh : mixedAfter new b=mixedBefore old b := by
    unfold mixedAfter mixedBefore
    rw [h0,h1,h2,h3]
  rw [mixed_after_local,mixed_before_zero] at hh
  apply sub_eq_zero.mp
  simpa only [p_sub_as_add] using hh

theorem chargeAux_swap (h : Nat → Bool → Bool → Fin 2) (n : Nat) (a b : List Bool) :
    chargeAux (fun i x y=>h i y x) n a b=chargeAux h n b a := by
  induction a generalizing n b with
  | nil => cases b <;> rfl
  | cons a as ih => cases b with
    | nil => rfl
    | cons b bs => simp only [chargeAux,ih]

theorem swap_conserved (old new : Nat → Bool → Bool → Fin 2)
    (hc : TestConserved old new) :
    TestConserved (fun i a b=>old i b a) (fun i a b=>new i b a) := by
  intro a b
  simpa only [charge,chargeAux_swap] using hc b a

theorem cell_score_constant (old new : Nat → Bool → Bool → Fin 2)
    (hc : TestConserved old new) (a b : Bool) : new 7 a b=new 7 false false := by
  have ha:=first_coordinate old new hc b
  have hb:=first_coordinate _ _ (swap_conserved old new hc) false
  cases a <;> cases b <;> simp_all

def AllSitesConserved (old new : Int → Bool → Bool → Fin 2) : Prop :=
  ∀ x : Int, TestConserved (fun i=>old (x+i)) (fun i=>new (x+i))

/-- No finite spatial/time clock assumption. Only the sixteen local physical
tests at every translation are required for this one-cell obstruction. -/
theorem all_sites (old new : Int → Bool → Bool → Fin 2)
    (hc : AllSitesConserved old new) (p : Int) (a b : Bool) :
    new p a b=new p false false := by
  have h:=cell_score_constant (fun i=>old (p-7+i)) (fun i=>new (p-7+i))
    (hc (p-7)) a b
  simpa only [show p-7+(7:Nat)=p by omega] using h



theorem chargeAux_constant (h : Nat → Bool → Bool → Fin 2)
    (hc : ∀ i a b, h i a b=h i false false) (i : Nat) (a b : List Bool) :
    chargeAux h i a b=0 := by
  induction a generalizing i b with
  | nil => rfl
  | cons a as ih =>
    cases b with
    | nil => rfl
    | cons b bs => simp only [chargeAux,hc,p_sub_self,p_zero_add,ih]

def leftSelector (a : Bool) : Fin 4 := if a then 1 else 0

theorem before_singleton (h : Nat → Bool → Bool → Fin 2) (a b : Bool) :
    charge h (before (leftSelector a)) (before (leftSelector b))=
      h 4 a b-h 4 false false := by
  cases a <;> cases b
  · change ((h 0 false false-h 0 false false)+((h 1 false false-h 1 false false)+((h 2 false false-h 2 false false)+((h 3 false false-h 3 false false)+((h 4 false false-h 4 false false)+((h 5 false false-h 5 false false)+((h 6 false false-h 6 false false)+((h 7 false false-h 7 false false)+((h 8 false false-h 8 false false)+((h 9 false false-h 9 false false)+((h 10 false false-h 10 false false)+((h 11 false false-h 11 false false)+((h 12 false false-h 12 false false)+((h 13 false false-h 13 false false)+((h 14 false false-h 14 false false)+((h 15 false false-h 15 false false)+0))))))))))))))))=h 4 false false-h 4 false false
    simp only [p_sub_self,p_add_zero,p_zero_add]
  · change ((h 0 false false-h 0 false false)+((h 1 false false-h 1 false false)+((h 2 false false-h 2 false false)+((h 3 false false-h 3 false false)+((h 4 false true-h 4 false false)+((h 5 false false-h 5 false false)+((h 6 false false-h 6 false false)+((h 7 false false-h 7 false false)+((h 8 false false-h 8 false false)+((h 9 false false-h 9 false false)+((h 10 false false-h 10 false false)+((h 11 false false-h 11 false false)+((h 12 false false-h 12 false false)+((h 13 false false-h 13 false false)+((h 14 false false-h 14 false false)+((h 15 false false-h 15 false false)+0))))))))))))))))=h 4 false true-h 4 false false
    simp only [p_sub_self,p_add_zero,p_zero_add]
  · change ((h 0 false false-h 0 false false)+((h 1 false false-h 1 false false)+((h 2 false false-h 2 false false)+((h 3 false false-h 3 false false)+((h 4 true false-h 4 false false)+((h 5 false false-h 5 false false)+((h 6 false false-h 6 false false)+((h 7 false false-h 7 false false)+((h 8 false false-h 8 false false)+((h 9 false false-h 9 false false)+((h 10 false false-h 10 false false)+((h 11 false false-h 11 false false)+((h 12 false false-h 12 false false)+((h 13 false false-h 13 false false)+((h 14 false false-h 14 false false)+((h 15 false false-h 15 false false)+0))))))))))))))))=h 4 true false-h 4 false false
    simp only [p_sub_self,p_add_zero,p_zero_add]
  · change ((h 0 false false-h 0 false false)+((h 1 false false-h 1 false false)+((h 2 false false-h 2 false false)+((h 3 false false-h 3 false false)+((h 4 true true-h 4 false false)+((h 5 false false-h 5 false false)+((h 6 false false-h 6 false false)+((h 7 false false-h 7 false false)+((h 8 false false-h 8 false false)+((h 9 false false-h 9 false false)+((h 10 false false-h 10 false false)+((h 11 false false-h 11 false false)+((h 12 false false-h 12 false false)+((h 13 false false-h 13 false false)+((h 14 false false-h 14 false false)+((h 15 false false-h 15 false false)+0))))))))))))))))=h 4 true true-h 4 false false
    simp only [p_sub_self,p_add_zero,p_zero_add]


theorem all_sites_old (old new : Int → Bool → Bool → Fin 2)
    (hc : AllSitesConserved old new) (p : Int) (a b : Bool) :
    old p a b=old p false false := by
  let x:=p-4
  have hn : ∀ (i : Nat) a b, new (x+i) a b=new (x+i) false false :=
    fun i a b=>all_sites old new hc (x+i) a b
  have he:=hc x (leftSelector a) (leftSelector b)
  change chargeAux (fun i=>new (x+i)) 0 _ _=charge _ _ _ at he
  rw [chargeAux_constant _ hn] at he
  rw [before_correct,before_correct,before_singleton] at he
  have ht:=sub_eq_zero.mp he.symm
  simpa only [x,show p-4+(4:Nat)=p by omega] using ht

/-- Complete classification of the translated two-pulse tests. The vacuum
baseline may vary arbitrarily with position and between the two times. -/
theorem all_sites_iff (old new : Int → Bool → Bool → Fin 2) :
    AllSitesConserved old new ↔
      (∀ p a b, old p a b=old p false false) ∧
      (∀ p a b, new p a b=new p false false) := by
  constructor
  · intro hc
    exact ⟨all_sites_old old new hc,all_sites old new hc⟩
  · rintro ⟨ho,hn⟩ x a b
    unfold charge
    rw [chargeAux_constant _ (fun i a b=>hn (x+i) a b),
      chargeAux_constant _ (fun i a b=>ho (x+i) a b)]

end Rule30WeightedCellResearch
