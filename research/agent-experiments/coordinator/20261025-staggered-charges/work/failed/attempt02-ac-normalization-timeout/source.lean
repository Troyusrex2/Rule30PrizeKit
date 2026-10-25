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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem mixed_before_zero (h : Nat → Bool → Bool → Fin 2) (b : Bool) :
    mixedBefore h b=0 := by
  cases b <;> simp [mixedBefore,selector,before,beforeRows,charge,chargeAux]
  all_goals weighted_parity_nf

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem mixed_after_local (h : Nat → Bool → Bool → Fin 2) (b : Bool) :
    mixedAfter h b=h 7 false b+h 7 true b := by
  cases b <;> simp [mixedAfter,selector,after,afterRows,charge,chargeAux]
  all_goals weighted_parity_nf

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

end Rule30WeightedCellResearch
