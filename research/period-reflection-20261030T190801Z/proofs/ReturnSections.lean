module
public import ReturnActions
/-! Core-only bridge for the existing PositiveAutomaton three-state table.
The states/table are prior catalog material, not a new automaton. -/
@[expose] public section
namespace ReturnSections
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration LeakDescent ReturnActions

inductive State where | A | B | C
  deriving DecidableEq
open State
def flip : State → Bool | A => false | B | C => true
def next : State → Bool → State
  | A,false => A
  | B,false => A
  | C,false => B
  | _,true => C
def memory (previous older : Bool) : State :=
  if previous then C else if older then B else A

def stateAfter (q : State) (x : Code) : Nat → State
  | 0 => q
  | n+1 => next (stateAfter q x n) (x n)
def act (q : State) (x : Code) : Code :=
  fun j => xor (x j) (flip (stateAfter q x j))
def run : List State → Code → Code
  | [],x => x
  | q::qs,x => act q (run qs x)
def sectionWord : List State → Code → Nat → List State
  | [],_,_ => []
  | q::qs,x,n => stateAfter q (run qs x) n :: sectionWord qs x n

theorem memory_next (p o b : Bool) : next (memory p o) b=memory b p := by
  cases p <;> cases o <;> cases b <;> rfl
theorem memory_flip (p o : Bool) : flip (memory p o)=(p||o) := by
  cases p <;> cases o <;> rfl
theorem after_two (q : State) (x : Code) (j : Nat) :
    stateAfter q x (j+2)=memory (x (j+1)) (x j) := by
  induction j with
  | zero => simp only [stateAfter];cases q <;> cases x 0 <;> cases x 1 <;> rfl
  | succ j ih =>
    change next (stateAfter q x (j+2)) (x (j+2))=_
    rw [ih,memory_next]

theorem act_A (x : Code) : act A x=T x := by
  funext j
  cases j with
  | zero => simp [act,stateAfter,flip,T]
  | succ j =>
    cases j with
    | zero => simp only [act,stateAfter,T];cases x 0 <;> rfl
    | succ j => simp only [act,T,after_two,memory_flip]

theorem run_A (p : Nat) (x : Code) : run (List.replicate p A) x=iter p x := by
  induction p with
  | zero => rfl
  | succ p ih => simp only [List.replicate_succ,run,ih,act_A,iter]

theorem after_add (q : State) (x : Code) (n j : Nat) :
    stateAfter q x (n+j)=stateAfter (stateAfter q x n) (drop n x) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change next (stateAfter q x (n+j)) (x (n+j))=
      next (stateAfter (stateAfter q x n) (drop n x) j) (drop n x j)
    rw [ih]
    rfl

theorem drop_act (q : State) (x : Code) (n : Nat) :
    drop n (act q x)=act (stateAfter q x n) (drop n x) := by
  funext j;simp only [drop,act,after_add]

theorem drop_run (w : List State) (x : Code) (n : Nat) :
    drop n (run w x)=run (sectionWord w x n) (drop n x) := by
  induction w with
  | nil => rfl
  | cons q qs ih => simp only [run,drop_act,sectionWord,ih]

theorem after_agree (q : State) (x y : Code) (n : Nat) (h : AgreeBelow n x y) :
    stateAfter q x n=stateAfter q y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stateAfter,ih (fun j hj => h j (by omega)),h n (by omega)]

theorem act_agree (q : State) (x y : Code) (n : Nat) (h : AgreeBelow n x y) :
    AgreeBelow n (act q x) (act q y) := by
  intro j hj
  simp only [act,h j hj,after_agree q x y j (fun k hk => h k (by omega))]

theorem run_agree (w : List State) (x y : Code) (n : Nat) (h : AgreeBelow n x y) :
    AgreeBelow n (run w x) (run w y) := by
  induction w with
  | nil => exact h
  | cons q qs ih => exact act_agree q _ _ n ih

theorem sections_agree (w : List State) (x y : Code) (n : Nat) (h : AgreeBelow n x y) :
    sectionWord w x n=sectionWord w y n := by
  induction w with
  | nil => rfl
  | cons q qs ih =>
    simp only [sectionWord,after_agree q _ _ n (run_agree qs x y n h),ih]

def returnWord (n P : Nat) (x : Code) : List State :=
  sectionWord (List.replicate P A) (join n x zero) n

theorem returnWord_eq (n P : Nat) (x : Code) :
    returnWord n P x=sectionWord (List.replicate P A) x n := by
  apply sections_agree
  intro j hj;exact join_low n x zero j hj

theorem drop_join (n : Nat) (x z : Code) : drop n (join n x z)=z := by
  funext j
  change join n x z (n+j)=z j
  rw [join_high n x z (n+j) (by omega)]
  congr 1;omega

/-- The symbolic three-state return word acts as the ACTUAL return tail. -/
theorem return_action (n P : Nat) (x z : Code) :
    tailReturn n P x z=run (returnWord n P x) z := by
  unfold tailReturn
  rw [←run_A P (join n x z),drop_run,drop_join]
  have same : sectionWord (List.replicate P A) (join n x z) n=returnWord n P x := by
    rw [returnWord_eq]
    apply sections_agree
    intro j hj;exact join_low n x z j hj
  rw [same]

def temporalWord (n : Nat) (x : Code) : Nat → List State
  | 0 => []
  | p+1 => stateAfter A (iter p x) n :: temporalWord n x p

theorem sections_temporal (n P : Nat) (x : Code) :
    sectionWord (List.replicate P A) x n=temporalWord n x P := by
  induction P with
  | zero => rfl
  | succ P ih => simp only [List.replicate_succ,sectionWord,run_A,ih,temporalWord]

theorem confined_words_equal (K P : Nat) (x y : Code) (h : Confined K 0 x y) :
    returnWord (K+3) P x=returnWord (K+3) P y := by
  rw [returnWord_eq,returnWord_eq,sections_temporal,sections_temporal]
  induction P with
  | zero => rfl
  | succ P ih =>
    change stateAfter A (iter P x) (K+3) :: temporalWord (K+3) x P=
      stateAfter A (iter P y) (K+3) :: temporalWord (K+3) y P
    rw [show K+3=(K+1)+2 by omega,after_two,after_two]
    rw [(h P (K+2) (by omega)).symm,(h P (K+1) (by omega)).symm,ih]

def DyadicWordInjective : Prop := ∀ (n : Nat) (x y : Code),
  0<n → x 0=true → y 0=true → returnWord n (2^n) x=returnWord n (2^n) y →
  AgreeBelow n x y

theorem word_injective_of_rigidity (rigid : SameEdgeRigidity) : DyadicWordInjective := by
  intro n x y hn hx hy equal
  apply return_injective_of_rigidity rigid n x y hn hx hy
  funext z
  rw [return_action,return_action,equal]

theorem rigidity_of_word_injective (inj : DyadicWordInjective) : SameEdgeRigidity := by
  intro K x y hx hy h
  have below:=inj (K+3) x y (by omega) hx hy (confined_words_equal K _ x y h)
  funext j
  by_cases low : j<K+3
  · exact below j low
  · exact (h 0 j (by omega)).symm

theorem rigidity_iff_word_injective : SameEdgeRigidity ↔ DyadicWordInjective :=
  ⟨word_injective_of_rigidity,rigidity_of_word_injective⟩

def AllReturnWordsInjective : Prop := ∀ (n P : Nat) (x y : Code),
  0<n → 0<P → x 0=true → y 0=true →
  AgreeBelow n (iter P x) x → AgreeBelow n (iter P y) y →
  returnWord n P x=returnWord n P y → AgreeBelow n x y

theorem all_return_words_of_rigidity (rigid : SameEdgeRigidity) : AllReturnWordsInjective := by
  intro n P x y hn hP hx hy fx fy equal
  have maps : tailReturn n P x=tailReturn n P y := by
    funext z;rw [return_action,return_action,equal]
  have rx:=prefix_factorization n P x fx
  have ry : Returns n P y (tailReturn n P x) := by
    rw [maps];exact prefix_factorization n P y fy
  have hc:=shared_return_confines n P hP x y _ rx ry
  have eq:=rigid (n+2*P) (join n x zero) (join n y zero)
    (by rw [join_low n x zero 0 hn];exact hx)
    (by rw [join_low n y zero 0 hn];exact hy) hc
  intro j hj
  have e:=congrFun eq j
  simpa only [join_low n x zero j hj,join_low n y zero j hj] using e

theorem rigidity_of_all_return_words (h : AllReturnWordsInjective) : SameEdgeRigidity := by
  apply rigidity_of_word_injective
  intro n x y hn hx hy equal
  exact h n (2^n) x y hn (Nat.two_pow_pos n) hx hy
    (prefix_period n x) (prefix_period n y) equal

theorem rigidity_iff_all_return_words : SameEdgeRigidity ↔ AllReturnWordsInjective :=
  ⟨all_return_words_of_rigidity,rigidity_of_all_return_words⟩

theorem canonical_iff_all_return_words : CanonicalClassification ↔ AllReturnWordsInjective :=
  classification_iff_same_edge.trans rigidity_iff_all_return_words

theorem sections_add (w : List State) (x : Code) (n j : Nat) :
    sectionWord w x (n+j)=sectionWord (sectionWord w x n) (drop n x) j := by
  induction w with
  | nil => rfl
  | cons q qs ih => simp only [sectionWord,after_add,drop_run,ih]

def single (b : Bool) : Code := fun j => if j=0 then b else false
def nextWord (w : List State) (b : Bool) : List State := sectionWord w (single b) 1
def output (w : List State) (b : Bool) : Bool := run w (single b) 0

theorem nextWord_read (w : List State) (x : Code) (n : Nat) :
    sectionWord w x (n+1)=nextWord (sectionWord w x n) (x n) := by
  rw [sections_add]
  apply sections_agree
  intro j hj
  have : j=0 := by omega
  subst j
  rfl

theorem output_read (w : List State) (x : Code) (j : Nat) :
    run w x j=output (sectionWord w x j) (x j) := by
  have h:=congrFun (drop_run w x j) 0
  have a : AgreeBelow 1 (drop j x) (single (x j)) := by
    intro k hk
    have : k=0 := by omega
    subst k;rfl
  have root:=run_agree (sectionWord w x j) _ _ 1 a 0 (by omega)
  simpa only [drop,Nat.add_zero,output] using h.trans root

def parity : List State → Bool
  | [] => false
  | q::qs => xor (flip q) (parity qs)

theorem output_parity (w : List State) (b : Bool) : output w b=xor b (parity w) := by
  induction w with
  | nil => change single b 0=xor b false;rw [Bool.xor_false];rfl
  | cons q qs ih =>
    change xor (output qs b) (flip q)=xor b (xor (flip q) (parity qs))
    rw [ih]
    cases b <;> cases flip q <;> cases parity qs <;> rfl

theorem fixed_prefix_iff (P n : Nat) (x : Code) :
    AgreeBelow n (iter P x) x ↔
      ∀ j,j<n → parity (sectionWord (List.replicate P A) x j)=false := by
  constructor
  · intro h j hj
    have e:=h j hj
    rw [←run_A P x,output_read] at e
    rw [output_parity] at e
    cases a:x j <;> cases b:parity (sectionWord (List.replicate P A) x j) <;> simp_all
  · intro h j hj
    rw [←run_A P x,output_read,output_parity,h j hj,Bool.xor_false]

-- Concrete obstructions to the naive cyclic-legality/primitive-period proof.
theorem period_drop_example : nextWord [B,C,C,C] false=[C,B,C,B] := by decide
theorem section_collision_example :
    nextWord [A,A,C,B] true=nextWord [A,A,C,C] true := by decide

theorem run_append (u v : List State) (x : Code) : run (u++v) x=run u (run v x) := by
  induction u with
  | nil => rfl
  | cons q qs ih => simp only [List.cons_append,run,ih]

theorem sections_append (u v : List State) (x : Code) (n : Nat) :
    sectionWord (u++v) x n=sectionWord u (run v x) n++sectionWord v x n := by
  induction u with
  | nil => rfl
  | cons q qs ih => simp only [List.cons_append,sectionWord,run_append,ih]

theorem nextWord_append (u v : List State) (b : Bool) :
    nextWord (u++v) b=nextWord u (output v b)++nextWord v b := by
  unfold nextWord
  rw [sections_append]
  have same : sectionWord u (run v (single b)) 1=sectionWord u (single (output v b)) 1 := by
    apply sections_agree
    intro j hj
    have : j=0 := by omega
    subst j
    rfl
  rw [same]

/-- Uniform period-doubling law. An old fixed-state branch stays square. -/
theorem double_even (w : List State) (h : parity w=false) (b : Bool) :
    nextWord (w++w) b=nextWord w b++nextWord w b := by
  rw [nextWord_append,output_parity,h,Bool.xor_false]

/-- An old root-swap (dead) state launches two different half-period words. -/
theorem double_odd (w : List State) (h : parity w=true) (b : Bool) :
    nextWord (w++w) b=nextWord w (!b)++nextWord w b := by
  rw [nextWord_append,output_parity,h]
  cases b <;> rfl

theorem nextWord_singleton (q : State) (b : Bool) : nextWord [q] b=[next q b] := rfl
theorem nextWord_snoc (u : List State) (q : State) (b : Bool) :
    nextWord (u++[q]) b=nextWord u (output [q] b)++[next q b] := by
  rw [nextWord_append,nextWord_singleton]

theorem distinct_children (u : List State) (q : State) :
    nextWord (u++[q]) false≠nextWord (u++[q]) true := by
  intro equal
  have last:=congrArg (fun w : List State => w.reverse.head?) equal
  simp only [nextWord_snoc,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.cons_append,List.head?_cons] at last
  cases q <;> simp only [next] at last <;> cases last

end ReturnSections
