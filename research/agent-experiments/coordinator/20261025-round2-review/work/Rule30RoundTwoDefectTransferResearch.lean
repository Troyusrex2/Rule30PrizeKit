module
public import Ruliology.CellularAutomata.Rule30Prize

/-! Formal cross-column transfer and an interval witness, following swarm's
R2-05. Eventual periodicity is an explicit conditional premise, not proved. -/
@[expose] public section
namespace Rule30RoundTwoDefectTransferResearch
open Ruliology.CellularAutomata
open Rule30Jen

def defect (P t : Nat) (x : Int) : Bool := xor (cell (t+P) x) (cell t x)

theorem xor_false_iff (a b : Bool) : xor a b=false ↔ a=b := by
  cases a <;> cases b <;> decide

theorem left_transfer (P t : Nat) (x : Int) :
    defect P t (x-1)=xor (defect P (t+1) x)
      (xor (cell (t+P) x || cell (t+P) (x+1)) (cell t x || cell t (x+1))) := by
  unfold defect
  rw [cell_left (t+P) x,cell_left t x,show t+1+P=t+P+1 by omega]
  cases cell (t+P+1) x <;> cases cell (t+1) x <;>
    cases cell (t+P) x <;> cases cell (t+P) (x+1) <;>
    cases cell t x <;> cases cell t (x+1) <;> decide

theorem left_zero (P t : Nat) (x : Int)
    (h0 : defect P t x=false) (h1 : defect P (t+1) x=false)
    (h2 : defect P t (x+1)=false) : defect P t (x-1)=false := by
  have e0 := (xor_false_iff _ _).mp h0
  have e2 := (xor_false_iff _ _).mp h2
  rw [left_transfer,h1,e0,e2]
  cases cell t x <;> cases cell t (x+1) <;> rfl

theorem zero_gate (P t : Nat)
    (h0 : defect P t 0=false) (h1 : defect P (t+1) 0=false) :
    defect P t (-1)=((!cell t 0) && defect P t 1) := by
  have e0 := (xor_false_iff _ _).mp h0
  rw [show (-1:Int)=0-1 by rfl,left_transfer,h1,e0]
  unfold defect
  simp only [Int.zero_add]
  cases cell t 0 <;> cases cell (t+P) 1 <;> cases cell t 1 <;> rfl

theorem white_terminal (P t : Nat)
    (h0 : defect P t 0=false) (h1 : defect P (t+1) 0=false)
    (hl : defect P t (-1)=true) : cell t 0=false ∧ defect P t 1=true := by
  rw [zero_gate P t h0 h1] at hl
  cases hc : cell t 0 <;> cases hd : defect P t 1 <;> simp_all

theorem triangle_zero (P b : Nat) : ∀ s x,
    (∀ t, s≤t → t≤s+b → defect P t x=false ∧ defect P t (x+1)=false) →
    defect P s (x-(b:Int))=false ∧ defect P s (x+1-(b:Int))=false := by
  induction b with
  | zero => intro s x h; simpa using h s (by omega) (by omega)
  | succ b ih =>
    intro s x h
    have a := ih s x (fun t ht he => h t ht (by omega))
    have c := ih (s+1) x (fun t ht he => h t (by omega) (by omega))
    have l := left_zero P s (x-(b:Int)) a.1 c.1 (by simpa only [show x-(b:Int)+1=x+1-(b:Int) by omega] using a.2)
    constructor
    · simpa only [show x-((b+1:Nat):Int)=x-(b:Int)-1 by omega] using l
    · simpa only [show x+1-((b+1:Nat):Int)=x-(b:Int) by omega] using a.1

theorem edge_defect (P m : Nat) (hP : 0<P) (hm : P≤m) :
    defect P (m-P) (-(m:Int))=true := by
  unfold defect
  rw [show m-P+P=m by omega,cell_left_edge m,
    cell_eq_false_of_lt (m-P) (-(m:Int)) (by omega)]
  rfl

/-- Every doubling-sized interval contains a right-neighbor defect at a white
center time under a hypothetically periodic center. This does not give a
positive density or a bound on the capacity of one terminal. -/
theorem white_terminal_interval (T P : Nat) (hP : 0<P)
    (hperiod : ∀ t, T≤t → cell (t+P) 0=cell t 0) (m : Nat) (hm : T+P≤m) :
    ∃ s, m-P≤s ∧ s≤2*m-P ∧ cell s 0=false ∧ defect P s 1=true := by
  apply Classical.byContradiction
  intro hn
  have hcenter : ∀ t, T≤t → defect P t 0=false := by
    intro t ht
    exact (xor_false_iff _ _).mpr (hperiod t ht)
  have hleft : ∀ t, m-P≤t → t≤2*m-P → defect P t (-1)=false := by
    intro t ht he
    cases hd : defect P t (-1) with
    | false => rfl
    | true =>
      have term := white_terminal P t (hcenter t (by omega)) (hcenter (t+1) (by omega)) hd
      exact False.elim (hn ⟨t,ht,he,term.1,term.2⟩)
  have htriangle := triangle_zero P (m-1) (m-P) (-1)
    (fun t ht he => ⟨hleft t ht (by omega),by simpa using hcenter t (by omega)⟩)
  have impossible : defect P (m-P) (-(m:Int))=false := by
    simpa only [show (-1:Int)-((m-1:Nat):Int)=-(m:Int) by omega] using htriangle.1
  rw [edge_defect P m hP (by omega)] at impossible
  cases impossible

end Rule30RoundTwoDefectTransferResearch
