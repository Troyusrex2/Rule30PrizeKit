module
public import Rule30ColumnReaderResearch

/-! The sound reader defines an equivalence relation at every width.
This does not prove that its rejecting sink has unequal traces. It supports
checking an exact finite trace partition using one representative per class. -/
@[expose] public section
namespace Rule30ReaderEquivalenceResearch
open Rule30ColumnReaderResearch
open Rule30CommonPastResearch (Actual)
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

abbrev Triple := Bool × Bool × Bool
abbrev Q3 := Nat × Nat × Nat
abbrev Q2 := Nat × Nat
def ab (s : Triple) : Symbol := (s.1,s.2.1)
def bc (s : Triple) : Symbol := (s.2.1,s.2.2)
def ac (s : Triple) : Symbol := (s.1,s.2.2)
def swap (s : Symbol) : Symbol := (s.2,s.1)
def advance3 (q : Q3) (s : Triple) : Q3 :=
  (next q.1 (ab s),next q.2.1 (bc s),next q.2.2 (ac s))
def run3 (q : Q3) : List Triple → Q3
  | [] => q
  | s::ss => run3 (advance3 q s) ss
def allowed3 : List Q3 := __TRIPLES__
def Inv3 (q : Q3) : Prop := accepted q.1=true → accepted q.2.1=true → accepted q.2.2=true
instance (q : Q3) : Decidable (Inv3 q) := by unfold Inv3;infer_instance
theorem initial3 : (0,0,0)∈allowed3 := by decide +kernel
theorem closed3_check : allowed3.all (fun q =>
    decide (∀ x y z : Bool, advance3 q (x,y,z)∈allowed3))=true := by decide +kernel
theorem inv3_check : allowed3.all (fun q => decide (Inv3 q))=true := by decide +kernel
theorem closed3 (q : Q3) (hq : q∈allowed3) (s : Triple) : advance3 q s∈allowed3 :=
  (of_decide_eq_true (List.all_eq_true.mp closed3_check q hq)) s.1 s.2.1 s.2.2
theorem inv3 (q : Q3) (hq : q∈allowed3) : Inv3 q :=
  of_decide_eq_true (List.all_eq_true.mp inv3_check q hq)
theorem run3_mem (ss : List Triple) : ∀ q, q∈allowed3 → run3 q ss∈allowed3 := by
  induction ss with
  | nil => exact fun _ h => h
  | cons s ss ih => intro q h;exact ih _ (closed3 q h s)
theorem run3_ab (ss : List Triple) (q : Q3) :
    (run3 q ss).1=run q.1 (ss.map ab) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (advance3 q s)
theorem run3_bc (ss : List Triple) (q : Q3) :
    (run3 q ss).2.1=run q.2.1 (ss.map bc) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (advance3 q s)
theorem run3_ac (ss : List Triple) (q : Q3) :
    (run3 q ss).2.2=run q.2.2 (ss.map ac) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (advance3 q s)
theorem transitive_words (ss : List Triple)
    (hab : accepted (run 0 (ss.map ab))=true)
    (hbc : accepted (run 0 (ss.map bc))=true) : accepted (run 0 (ss.map ac))=true := by
  have h := inv3 _ (run3_mem ss _ initial3)
  unfold Inv3 at h
  rw [run3_ab,run3_bc,run3_ac] at h
  exact h hab hbc

def advance2 (q : Q2) (s : Symbol) : Q2 := (next q.1 s,next q.2 (swap s))
def run2 (q : Q2) : List Symbol → Q2
  | [] => q
  | s::ss => run2 (advance2 q s) ss
def allowed2 : List Q2 := __PAIRS__
def Inv2 (q : Q2) : Prop := accepted q.1=accepted q.2
instance (q : Q2) : Decidable (Inv2 q) := by unfold Inv2;infer_instance
theorem initial2 : (0,0)∈allowed2 := by decide +kernel
theorem closed2_check : allowed2.all (fun q =>
    decide (∀ x y : Bool, advance2 q (x,y)∈allowed2))=true := by decide +kernel
theorem inv2_check : allowed2.all (fun q => decide (Inv2 q))=true := by decide +kernel
theorem closed2 (q : Q2) (hq : q∈allowed2) (s : Symbol) : advance2 q s∈allowed2 :=
  (of_decide_eq_true (List.all_eq_true.mp closed2_check q hq)) s.1 s.2
theorem inv2 (q : Q2) (hq : q∈allowed2) : Inv2 q :=
  of_decide_eq_true (List.all_eq_true.mp inv2_check q hq)
theorem run2_mem (ss : List Symbol) : ∀ q, q∈allowed2 → run2 q ss∈allowed2 := by
  induction ss with
  | nil => exact fun _ h => h
  | cons s ss ih => intro q h;exact ih _ (closed2 q h s)
theorem run2_first (ss : List Symbol) (q : Q2) : (run2 q ss).1=run q.1 ss := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (advance2 q s)
theorem run2_second (ss : List Symbol) (q : Q2) : (run2 q ss).2=run q.2 (ss.map swap) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (advance2 q s)
theorem symmetric_words (ss : List Symbol) :
    accepted (run 0 ss)=accepted (run 0 (ss.map swap)) := by
  have h := inv2 _ (run2_mem ss _ initial2)
  unfold Inv2 at h
  rw [run2_first,run2_second] at h
  exact h

def allowed1 : List Nat := [0,3,12]
theorem initial1 : 0∈allowed1 := by decide +kernel
theorem closed1_check : allowed1.all (fun q =>
    decide (∀ x : Bool, next q (x,x)∈allowed1))=true := by decide +kernel
theorem inv1_check : allowed1.all (fun q => accepted q)=true := by decide +kernel
theorem diagonal_mem (ss : List Bool) :
    ∀ q, q∈allowed1 → run q (ss.map (fun x => (x,x)))∈allowed1 := by
  induction ss with
  | nil => exact fun _ h => h
  | cons s ss ih =>
    intro q h
    exact ih _ ((of_decide_eq_true (List.all_eq_true.mp closed1_check q h)) s)
theorem reflexive_words (ss : List Bool) : accepted (run 0 (ss.map (fun x => (x,x))))=true :=
  List.all_eq_true.mp inv1_check _ (diagonal_mem ss 0 initial1)

def take {α : Type} (x : Nat → α) : Nat → List α
  | 0 => []
  | n+1 => x 0 :: take (fun j => x (j+1)) n
theorem map_take {α β : Type} (f : α → β) (x : Nat → α) (n : Nat) :
    (take x n).map f=take (fun j => f (x j)) n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [take,List.map_cons];rw [ih]
theorem take_pair (x : Nat → Symbol) (n : Nat) : take x n=takeRow x n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [take,takeRow];rw [ih]
def Related (x y : Nat → Bool) (n : Nat) : Prop :=
  accepted (run 0 (take (fun j => (x j,y j)) n))=true

theorem related_refl (x : Nat → Bool) (n : Nat) : Related x x n := by
  have h := reflexive_words (take x n)
  simpa only [map_take,Related] using h
theorem related_symm (x y : Nat → Bool) (n : Nat) : Related x y n ↔ Related y x n := by
  have h := symmetric_words (take (fun j => (x j,y j)) n)
  simp only [map_take,swap] at h
  unfold Related
  rw [h]
theorem related_trans (x y z : Nat → Bool) (n : Nat)
    (hxy : Related x y n) (hyz : Related y z n) : Related x z n := by
  have h := transitive_words (take (fun j => (x j,y j,z j)) n)
  simp only [map_take,ab,bc,ac] at h
  exact h hxy hyz
theorem shared_representative (x y r : Nat → Bool) (n : Nat)
    (hx : Related x r n) (hy : Related y r n) : Related x y n :=
  related_trans x r y n hx ((related_symm y r n).mp hy)

theorem related_sound (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (n : Nat) (hn : 0<n) (h : Related (a 0) (b 0) n) : ∀ t, a t (n-1)=b t (n-1) := by
  apply reader_sound a b ha hb n hn
  simpa only [Related,take_pair] using h

end Rule30ReaderEquivalenceResearch
