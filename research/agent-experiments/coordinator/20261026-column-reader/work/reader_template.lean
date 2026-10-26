module
public import Rule30CommonPastResearch

/-! A learned recognizer with a checked unbounded soundness certificate.
Accepted words have equal last-column traces. Completeness is NOT asserted:
rejected words have not all been proved to have different traces. -/
@[expose] public section
namespace Rule30ColumnReaderResearch
open Ruliology.CellularAutomata
open Rule30CommonPastResearch (Actual march)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

abbrev Symbol := Bool × Bool
def zero : Symbol := (false,false)
def code (s : Symbol) : Nat := (if s.1 then 2 else 0)+(if s.2 then 1 else 0)
def table : List (List Nat) := __TABLE__
def next (q : Nat) (s : Symbol) : Nat := (table.getD q []).getD (code s) 15
def accepted (q : Nat) : Bool := q==0 || q==3 || q==12 || q==16

def run (q : Nat) : List Symbol → Nat
  | [] => q
  | s::ss => run (next q s) ss
def update (p r s : Symbol) : Symbol :=
  (xor s.1 (p.1 || r.1),xor s.2 (p.2 || r.2))
def change (p r : Symbol) : List Symbol → List Symbol
  | [] => []
  | s::ss => update p r s :: change s p ss
def stepWord (ss : List Symbol) := change zero zero ss
def lastPair (d : Symbol) : List Symbol → Symbol
  | [] => d
  | s::ss => lastPair s ss

structure Coupled where
  raw : Nat
  transformed : Nat
  previous : Symbol
  older : Symbol
  deriving DecidableEq
def initial : Coupled := ⟨0,0,zero,zero⟩
def advance (q : Coupled) (s : Symbol) : Coupled :=
  ⟨next q.raw s,next q.transformed (update q.previous q.older s),s,q.previous⟩
def runCoupled (q : Coupled) : List Symbol → Coupled
  | [] => q
  | s::ss => runCoupled (advance q s) ss
def allowed : List Coupled := __ALLOWED__
def Invariant (q : Coupled) : Prop :=
  accepted q.raw=accepted q.transformed ∧
    (accepted q.raw=true → q.previous.1=q.previous.2)
instance (q : Coupled) : Decidable (Invariant q) := by unfold Invariant;infer_instance

theorem initial_mem : initial∈allowed := by decide +kernel
theorem closed_check : allowed.all
    (fun q => decide (∀ a b : Bool, advance q (a,b)∈allowed))=true := by decide +kernel
theorem invariant_check : allowed.all (fun q => decide (Invariant q))=true := by decide +kernel

theorem closed (q : Coupled) (hq : q∈allowed) (s : Symbol) : advance q s∈allowed := by
  have he := List.all_eq_true.mp closed_check q hq
  exact (of_decide_eq_true he) s.1 s.2
theorem invariant (q : Coupled) (hq : q∈allowed) : Invariant q :=
  of_decide_eq_true (List.all_eq_true.mp invariant_check q hq)

theorem run_mem (ss : List Symbol) : ∀ q, q∈allowed → runCoupled q ss∈allowed := by
  induction ss with
  | nil => exact fun _ h => h
  | cons s ss ih => intro q hq;exact ih (advance q s) (closed q hq s)

theorem raw_run (ss : List Symbol) (q : Coupled) :
    (runCoupled q ss).raw=run q.raw ss := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => simpa only [runCoupled,run,advance] using ih (advance q s)
theorem transformed_run (ss : List Symbol) (q : Coupled) :
    (runCoupled q ss).transformed=run q.transformed (change q.previous q.older ss) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => simpa only [runCoupled,run,change,advance] using ih (advance q s)
theorem previous_run (ss : List Symbol) (q : Coupled) :
    (runCoupled q ss).previous=lastPair q.previous ss := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => simpa only [runCoupled,lastPair,advance] using ih (advance q s)

theorem acceptance_invariant (ss : List Symbol) :
    accepted (run 0 ss)=accepted (run 0 (stepWord ss)) := by
  have he := (invariant (runCoupled initial ss) (run_mem ss initial initial_mem)).1
  simpa only [raw_run,transformed_run,initial,stepWord] using he

theorem accepted_last_equal (ss : List Symbol) (hs : accepted (run 0 ss)=true) :
    (lastPair zero ss).1=(lastPair zero ss).2 := by
  have he := (invariant (runCoupled initial ss) (run_mem ss initial initial_mem)).2
  have hraw : accepted (runCoupled initial ss).raw=true := by
    simpa only [raw_run,initial] using hs
  simpa only [previous_run,initial] using he hraw

def takeRow (x : Nat → Symbol) : Nat → List Symbol
  | 0 => []
  | n+1 => x 0 :: takeRow (fun j => x (j+1)) n
def rowStep (p r : Symbol) (x : Nat → Symbol) : Nat → Symbol
  | 0 => update p r (x 0)
  | 1 => update (x 0) p (x 1)
  | j+2 => update (x (j+1)) (x j) (x (j+2))

theorem row_shift (p r : Symbol) (x : Nat → Symbol) :
    rowStep (x 0) p (fun j => x (j+1))=(fun j => rowStep p r x (j+1)) := by
  funext j
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl
theorem change_take (n : Nat) (p r : Symbol) (x : Nat → Symbol) :
    change p r (takeRow x n)=takeRow (rowStep p r x) n := by
  induction n generalizing p r x with
  | zero => rfl
  | succ n ih =>
    simp only [takeRow,change]
    rw [ih,row_shift p r x]
    rfl

theorem rowStep_march (a b : Nat → Bool) :
    rowStep zero zero (fun j => (a j,b j))=(fun j => (march a j,march b j)) := by
  funext j
  cases j with
  | zero => simp [rowStep,update,zero,march]
  | succ j => cases j <;> simp [rowStep,update,zero,march]

theorem prefix_step (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (t n : Nat) : stepWord (takeRow (fun j => (a t j,b t j)) n)=
      takeRow (fun j => (a (t+1) j,b (t+1) j)) n := by
  unfold stepWord
  rw [change_take,rowStep_march]
  congr 1
  funext j
  rw [ha t j,hb t j]

theorem last_take (n : Nat) (hn : 0<n) (x : Nat → Symbol) (d : Symbol) :
    lastPair d (takeRow x n)=x (n-1) := by
  induction n generalizing x d with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change lastPair (x 0) (takeRow (fun j => x (j+1)) (n+1))=x ((n+1+1)-1)
      rw [ih (by omega)]
      congr 1 <;> omega

/-- Unbounded soundness only. No converse for rejected words is asserted. -/
theorem reader_sound (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (n : Nat) (hn : 0<n)
    (hs : accepted (run 0 (takeRow (fun j => (a 0 j,b 0 j)) n))=true) :
    ∀ t, a t (n-1)=b t (n-1) := by
  have he : ∀ t, accepted (run 0 (takeRow (fun j => (a t j,b t j)) n))=true := by
    intro t
    induction t with
    | zero => exact hs
    | succ t ih =>
      have hp := acceptance_invariant (takeRow (fun j => (a t j,b t j)) n)
      rw [prefix_step a b ha hb t n] at hp
      exact hp.symm.trans ih
  intro t
  have hp := accepted_last_equal (takeRow (fun j => (a t j,b t j)) n) (he t)
  simpa only [last_take n hn] using hp

end Rule30ColumnReaderResearch
