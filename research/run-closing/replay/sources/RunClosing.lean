module
public import RunClosingData

/-!
# Universal inverse synchronization, a run criterion, and exact damage

This is a structural tool for the ancestry attempt, not a prize solution.
The transfer map is the existing Feynman predecessor map from the kit,
read in scan order. The finite-semigroup certificate gives an all-word
recognizer. A zero-delimited black run of length 3*k+1 followed by one
more input cell resets every inverse state, for EVERY k.

No claim is made that legal Rule30 forced rows always contain these runs.
-/
@[expose] public section
namespace RunClosing

abbrev State := Bool × Bool
def transfer (b : Bool) (s : State) : State := (xor b (s.1 || s.2),s.1)
def scan : List Bool → State → State
  | [],s => s
  | b::w,s => scan w (transfer b s)

def Synchronized (w : List Bool) : Prop :=
  ∀ a b c d : Bool, scan w (a,b)=scan w (c,d)

def patternStep (q : Nat) (b : Bool) : Nat :=
  match q with
  | 0 => if b then 0 else 1
  | 1 => if b then 2 else 1
  | 2 => if b then 3 else 4
  | 3 => 1
  | 4 => 5
  | _ => 5

def patternRead : Nat → List Bool → Nat
  | q,[] => q
  | q,b::w => patternRead (patternStep q b) w

abbrev Index := Fin 41
def record (i : Index) := records[i.val]?.getD (228,0,0,0)
def byte (i : Index) := (record i).1
def phase (i : Index) := (record i).2.1
def nextVal (i : Index) (b : Bool) :=
  if b then (record i).2.2.2 else (record i).2.2.1

theorem next_bound : ∀ i : Index, ∀ b : Bool, nextVal i b<41 := by decide
def advance (i : Index) (b : Bool) : Index := ⟨nextVal i b,next_bound i b⟩
def applyMap (n : Nat) (s : State) : State :=
  let k := s.1.toNat+2*s.2.toNat
  (n.testBit (2*k),n.testBit (2*k+1))
def Constant (i : Index) : Prop :=
  ∀ a b c d : Bool, applyMap (byte i) (a,b)=applyMap (byte i) (c,d)

theorem table_transition : ∀ i : Index, ∀ b a c : Bool,
    applyMap (byte (advance i b)) (a,c)=transfer b (applyMap (byte i) (a,c)) ∧
    phase (advance i b)=patternStep (phase i) b := by decide

theorem table_constant : ∀ i : Index, Constant i ↔ phase i=5 := by
  unfold Constant
  decide

def initial : Index := ⟨0,by decide⟩
theorem initial_map (s : State) : applyMap (byte initial) s=s := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> decide
theorem initial_phase : phase initial=0 := by decide

def readIndex : Index → List Bool → Index
  | i,[] => i
  | i,b::w => readIndex (advance i b) w

theorem map_read (w : List Bool) (i : Index) (s : State) :
    applyMap (byte (readIndex i w)) s=scan w (applyMap (byte i) s) := by
  induction w generalizing i s with
  | nil => rfl
  | cons b w ih =>
    simp only [readIndex,scan,ih]
    rw [(table_transition i b s.1 s.2).1]

theorem phase_read (w : List Bool) (i : Index) :
    phase (readIndex i w)=patternRead (phase i) w := by
  induction w generalizing i with
  | nil => rfl
  | cons b w ih =>
    simp only [readIndex,patternRead,ih,(table_transition i b false false).2]

/-- Exact synchronization test for arbitrary finite input words. -/
theorem synchronized_iff_pattern (w : List Bool) :
    Synchronized w ↔ patternRead 0 w=5 := by
  simpa only [Constant,Synchronized,map_read,initial_map,phase_read,initial_phase] using
    table_constant (readIndex initial w)

theorem scan_append (u v : List Bool) (s : State) :
    scan (u++v) s=scan v (scan u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons b u ih => simpa only [List.cons_append,scan] using ih (transfer b s)

theorem pattern_append (u v : List Bool) (q : Nat) :
    patternRead q (u++v)=patternRead (patternRead q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons b u ih => simpa only [List.cons_append,patternRead] using ih (patternStep q b)

theorem ones_pattern (k : Nat) :
    patternRead 1 (List.replicate (3*k+1) true)=2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 3*(k+1)+1=(3*k+1)+3 by omega,←List.replicate_append_replicate,pattern_append,ih]
    rfl

/-- An unbounded run family, not a bounded word table. -/
theorem run_resets (k : Nat) (b : Bool) :
    Synchronized ([false]++List.replicate (3*k+1) true++[false,b]) := by
  rw [synchronized_iff_pattern]
  rw [pattern_append,pattern_append]
  change patternRead (patternRead 1 (List.replicate (3*k+1) true)) [false,b]=5
  rw [ones_pattern]
  cases b <;> rfl

theorem synchronized_context (u w v : List Bool) (h : Synchronized w) :
    Synchronized (u++w++v) := by
  intro a b c d
  simp only [scan_append]
  rw [h (scan u (a,b)).1 (scan u (a,b)).2 (scan u (c,d)).1 (scan u (c,d)).2]

def HasResetRun (w : List Bool) : Prop :=
  ∃ u k b v, w=(u++[false]++List.replicate (3*k+1) true++[false,b])++v

def SuffixRun (w : List Bool) (r : Nat) : Prop :=
  ∃ u k, w=u++[false]++List.replicate (3*k+r) true
def PendingRun (w : List Bool) : Prop :=
  ∃ u k, w=u++[false]++List.replicate (3*k+1) true++[false]

def Good (w : List Bool) : Nat → Prop
  | 0 => True
  | 1 => SuffixRun w 0
  | 2 => SuffixRun w 1
  | 3 => SuffixRun w 2
  | 4 => PendingRun w
  | _ => HasResetRun w

theorem suffix_zero (w : List Bool) : SuffixRun (w++[false]) 0 := by
  exact ⟨w,0,by simp⟩

theorem suffix_one (w : List Bool) (r : Nat) (h : SuffixRun w r) :
    SuffixRun (w++[true]) (r+1) := by
  obtain ⟨u,k,hk⟩ := h
  refine ⟨u,k,?_⟩
  rw [hk,show 3*k+(r+1)=(3*k+r)+1 by omega,List.replicate_succ']
  simp only [List.append_assoc]

theorem suffix_three (w : List Bool) (h : SuffixRun w 3) : SuffixRun w 0 := by
  obtain ⟨u,k,hk⟩ := h
  refine ⟨u,k+1,?_⟩
  rw [show 3*(k+1)+0=3*k+3 by omega]
  exact hk

theorem pending_zero (w : List Bool) (h : SuffixRun w 1) : PendingRun (w++[false]) := by
  obtain ⟨u,k,hk⟩ := h
  exact ⟨u,k,by rw [hk]⟩

theorem pending_done (w : List Bool) (b : Bool) (h : PendingRun w) :
    HasResetRun (w++[b]) := by
  obtain ⟨u,k,hk⟩ := h
  refine ⟨u,k,b,[],?_⟩
  rw [hk]
  simp only [List.append_nil,List.append_assoc,List.cons_append,List.nil_append]

theorem reset_append (w : List Bool) (b : Bool) (h : HasResetRun w) :
    HasResetRun (w++[b]) := by
  obtain ⟨u,k,c,v,hv⟩ := h
  exact ⟨u,k,c,v++[b],by rw [hv,List.append_assoc]⟩

theorem good_step (w : List Bool) (b : Bool) :
    ∀ q, Good w q → Good (w++[b]) (patternStep q b)
  | 0,h => by cases b <;> first | exact suffix_zero w | exact True.intro
  | 1,h => by
      cases b
      · exact suffix_zero w
      · exact suffix_one w 0 h
  | 2,h => by
      cases b
      · exact pending_zero w h
      · exact suffix_one w 1 h
  | 3,h => by
      cases b
      · exact suffix_zero w
      · exact suffix_three _ (suffix_one w 2 h)
  | 4,h => pending_done w b h
  | q+5,h => reset_append w b h

theorem good_read (u w : List Bool) (q : Nat) (h : Good u q) :
    Good (u++w) (patternRead q w) := by
  induction w generalizing u q with
  | nil => simpa only [List.append_nil,patternRead] using h
  | cons b w ih =>
    have he := ih (u++[b]) (patternStep q b) (good_step u b q h)
    simpa only [patternRead,List.append_assoc,List.singleton_append] using he

/-- Necessary as well as sufficient: complete inverse merging is exactly
the occurrence of a 0-delimited 3*k+1 black run with a following cell. -/
theorem synchronized_iff_reset_run (w : List Bool) : Synchronized w ↔ HasResetRun w := by
  constructor
  · intro h
    have hp := (synchronized_iff_pattern w).mp h
    have hg := good_read [] w 0 True.intro
    simpa only [List.nil_append,hp,Good] using hg
  · rintro ⟨u,k,b,v,hv⟩
    rw [hv]
    simpa only [List.append_assoc] using synchronized_context u _ v (run_resets k b)

def xorPair (x y : State) : State := (xor x.1 y.1,xor x.2 y.2)
def damageStep (x d : State) : State :=
  (xor (x.1||x.2) ((xor x.1 d.1)||(xor x.2 d.2)),d.1)

theorem damage_identity (b : Bool) (x d : State) :
    xorPair (transfer b x) (transfer b (xorPair x d))=damageStep x d := by
  rcases x with ⟨a,c⟩
  rcases d with ⟨e,f⟩
  cases b <;> cases a <;> cases c <;> cases e <;> cases f <;> rfl

def process : List Bool → State → State → State × State
  | [],x,d => (x,d)
  | b::w,x,d => process w (transfer b x) (damageStep x d)

theorem xorPair_cancel (x y : State) : xorPair x (xorPair x y)=y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem xorPair_zero (x y : State) : xorPair x y=(false,false) ↔ x=y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem process_damage (w : List Bool) (x d : State) :
    (process w x d).2=xorPair (scan w x) (scan w (xorPair x d)) := by
  induction w generalizing x d with
  | nil =>
    change d=xorPair x (xorPair x d)
    exact (xorPair_cancel x d).symm
  | cons b w ih =>
    simp only [process,scan,ih]
    rw [←damage_identity,xorPair_cancel]

/-- The corrected top-slice process is exactly universal inverse merging. -/
theorem all_damage_dies_iff (w : List Bool) (x : State) :
    (∀ a b : Bool, (process w x (a,b)).2=(false,false)) ↔ Synchronized w := by
  constructor
  · intro h a b c d
    have hx (y : State) : scan w x=scan w y := by
      have hi := h (xorPair x y).1 (xorPair x y).2
      rw [process_damage,xorPair_cancel] at hi
      exact (xorPair_zero _ _).mp hi
    exact (hx (a,b)).symm.trans (hx (c,d))
  · intro h a b
    rw [process_damage,xorPair_zero]
    exact h x.1 x.2 (xorPair x (a,b)).1 (xorPair x (a,b)).2

def segment (f : Nat → Bool) : Nat → Nat → List Bool
  | _,0 => []
  | a,n+1 => f a::segment f (a+1) n

def TailClosing (f : Nat → Bool) : Prop :=
  ∀ d, ∃ a n, d≤a ∧ Synchronized (segment f a n)

theorem scan_false (n : Nat) :
    scan (List.replicate n false) (false,false)=(false,false) ∧
    scan (List.replicate n false) (true,true)=(true,true) := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simpa only [List.replicate_succ,scan,transfer,Bool.false_or,
      Bool.true_or,Bool.false_xor] using ih

theorem zeros_not_synchronized (n : Nat) : ¬Synchronized (List.replicate n false) := by
  intro h
  have he := h false false true true
  rw [(scan_false n).1,(scan_false n).2] at he
  cases he

/-- Universal tail closing already excludes every eventually white row.
Thus it is a substantive finite-ancestry claim, not a routine automaton fact. -/
theorem tail_closing_not_finite (f : Nat → Bool) (hc : TailClosing f) :
    ¬∃ W, ∀ k, W≤k → f k=false := by
  rintro ⟨W,hW⟩
  obtain ⟨a,n,ha,hs⟩ := hc W
  have seg : ∀ m a, W≤a → segment f a m=List.replicate m false := by
    intro m
    induction m with
    | zero => intro a ha;rfl
    | succ m ih => intro a ha;simp only [segment,List.replicate_succ,hW a ha,ih (a+1) (by omega)]
  rw [seg n a ha] at hs
  exact zeros_not_synchronized n hs

theorem segment_add (f : Nat → Bool) (a m n : Nat) :
    segment f a (m+n)=segment f a m++segment f (a+m) n := by
  induction m generalizing a with
  | zero => simp [segment]
  | succ m ih =>
    rw [show (m+1)+n=(m+n)+1 by omega]
    simp only [segment,List.cons_append,ih]
    rw [show a+1+m=a+(m+1) by omega]

theorem tail_closing_iff (f : Nat → Bool) :
    TailClosing f ↔ ∀ d, ∃ n, Synchronized (segment f d n) := by
  constructor
  · intro h d
    obtain ⟨a,n,ha,hs⟩ := h d
    refine ⟨(a-d)+n,?_⟩
    rw [segment_add,show d+(a-d)=a by omega]
    have he := synchronized_context (segment f d (a-d)) (segment f a n) [] hs
    simpa only [List.append_nil] using he
  · intro h d
    obtain ⟨n,hn⟩ := h d
    exact ⟨d,n,Nat.le_refl _,hn⟩

/-- One physical forward row, at depths k+1, in left-half coordinates. -/
def forward (a : Nat → Bool) (k : Nat) : Bool :=
  xor (a (k+2)) (a (k+1)||a k)

theorem forward_rule (a : Nat → Bool) (k : Nat) :
    forward a k=Ruliology.CellularAutomata.Rule30Jen.rule (a (k+2)) (a (k+1)) (a k) := rfl

theorem forward_transfer (a : Nat → Bool) (k : Nat) :
    transfer (forward a k) (a (k+1),a k)=(a (k+2),a (k+1)) := by
  simp only [transfer,forward]
  cases a (k+2) <;> cases (a (k+1)||a k) <;> rfl

theorem reference_scan (a : Nat → Bool) (d n : Nat) :
    scan (segment (forward a) d n) (a (d+1),a d)=(a (d+n+1),a (d+n)) := by
  induction n generalizing d with
  | zero => simp [segment,scan]
  | succ n ih =>
    simp only [segment,scan,forward_transfer]
    have he := ih (d+1)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he

def RowClosing (a : Nat → Bool) : Prop :=
  ∀ d, ∃ n, ∀ p q : Bool,
    (process (segment (forward a) d n) (a (d+1),a d) (p,q)).2=(false,false)

/-- The top-slice conjecture is exactly recurrent inverse synchronization
on the NEXT physical row, not on an unrelated abstract input word. -/
theorem row_closing_iff (a : Nat → Bool) : RowClosing a ↔ TailClosing (forward a) := by
  rw [tail_closing_iff]
  constructor
  · intro h d
    obtain ⟨n,hn⟩ := h d
    exact ⟨n,(all_damage_dies_iff _ _).mp hn⟩
  · intro h d
    obtain ⟨n,hn⟩ := h d
    exact ⟨n,(all_damage_dies_iff _ _).mpr hn⟩

theorem row_closing_iff_runs (a : Nat → Bool) :
    RowClosing a ↔ ∀ d, ∃ k n, d≤k ∧ HasResetRun (segment (forward a) k n) := by
  rw [row_closing_iff]
  simp only [TailClosing,synchronized_iff_reset_run]

theorem row_closing_not_finite (a : Nat → Bool) (hc : RowClosing a) :
    ¬∃ W, ∀ k, W≤k → a k=false := by
  rintro ⟨W,hW⟩
  apply tail_closing_not_finite (forward a) ((row_closing_iff a).mp hc)
  refine ⟨W,?_⟩
  intro k hk
  simp only [forward,hW k hk,hW (k+1) (by omega),hW (k+2) (by omega)]
  rfl

def oddBlack (G : Nat → Bool) (t : Nat) : Bool :=
  if t%2=0 then !G (t/2) else true
def evenBlack (F : Nat → Bool) (t : Nat) : Bool :=
  if t%2=0 then true else F (t/2)

/-- Odd-time slices require the OTHER boundary phase. An analysis of only
oddBlack row zero does not cover every slice in the damage-envelope argument. -/
theorem boundary_shift_one (G : Nat → Bool) (t : Nat) :
    oddBlack G (t+1)=evenBlack (fun r => !G (r+1)) t := by
  unfold oddBlack evenBlack
  by_cases he : t%2=0
  · have hn : ¬(t+1)%2=0 := by omega
    simp only [he,hn,ite_true,ite_false]
  · have hn : (t+1)%2=0 := by omega
    have hd : (t+1)/2=t/2+1 := by omega
    simp only [he,hn,ite_true,ite_false,hd]

end RunClosing
