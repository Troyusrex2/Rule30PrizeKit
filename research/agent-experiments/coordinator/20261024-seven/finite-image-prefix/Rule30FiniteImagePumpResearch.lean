import Rule30FinitePastFrontResearch
import Rule30FiniteWordAppendResearch

/-! Finite predecessors with arbitrarily long constant output blocks.
A uniform lower bound on signed unit-scale reader scores over these
actual images forces both costs at the absorbing state to be nonnegative. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Rule30FiniteImagePumpResearch
open Ruliology.CellularAutomata.Rule30ZeroBoundary
open Rule30FiniteLeftWordResearch (row next row_support zrow_support zrow_prefix)
open Rule30CriticalChargeOneCoreResearch (left)
open Rule30FiniteWordAppendResearch (getD_append_right row_append_prefix row_middle row_tail_shift)

def local2 (a b c d e : Bool) : Bool :=
  xor (xor e (d || c)) (xor d (c || b) || xor c (b || a))

theorem zero_time {L : Nat → Bool} (h : L 0=false) : zrow L 0=L := by
  funext d
  cases d with
  | zero => exact h.symm
  | succ d => rfl

theorem two_local {L : Nat → Bool} (h : L 0=false) (k : Nat) :
    zrow L 2 (k+2)=local2 (L k) (L (k+1)) (L (k+2)) (L (k+3)) (L (k+4)) := by
  rw [show 2=1+1 by omega,zrow_succ,zrow_succ,zrow_succ,zrow_succ]
  simp only [zero_time h]
  rfl

def span (b : Bool) (n : Nat) : Nat := if b then 3*n else n
def pattern (b : Bool) (d : Nat) : Bool := if b then decide (d%3≠0) else false

def base (b : Bool) : List Bool :=
  (List.range 32).map (fun i=>zrow left 2 (i+1)) ++
    (if b then [false,true,true,false] else [false,false,false,false])

def predecessor (b : Bool) (n d : Nat) : Bool :=
  if d≤36 then row (base b) d
  else if d≤36+span b n then pattern b d else decide (d=37+span b n)

theorem base_length (b : Bool) : (base b).length=36 := by cases b <;> simp [base]
theorem span_zero (b : Bool) : span b 0=0 := by cases b <;> rfl
theorem predecessor_wall (b : Bool) (n : Nat) : predecessor b n 0=false := rfl

theorem base_pattern (b : Bool) : ∀ d,33≤d → d≤36 → row (base b) d=pattern b d := by
  intro d h0 h1
  rcases (show d=33 ∨ d=34 ∨ d=35 ∨ d=36 by omega) with rfl | rfl | rfl | rfl <;>
    cases b <;> decide +kernel

theorem predecessor_bulk (b : Bool) (n i : Nat) (h0 : 33≤i) (h1 : i≤36+span b n) :
    predecessor b n i=pattern b i := by
  by_cases hi : i≤36
  · simp only [predecessor,hi,↓reduceIte]
    exact base_pattern b i h0 hi
  · simp [predecessor,hi,h1]

theorem pattern_shift (b : Bool) (n i : Nat) : pattern b (i+span b n)=pattern b i := by
  cases b with
  | false => rfl
  | true => simp [pattern,span,Nat.add_mod]

theorem local_pattern (b : Bool) (k : Nat) :
    local2 (pattern b k) (pattern b (k+1)) (pattern b (k+2))
      (pattern b (k+3)) (pattern b (k+4))=b := by
  cases b with
  | false => rfl
  | true =>
    have h : k%3=0 ∨ k%3=1 ∨ k%3=2 := by omega
    rcases h with h | h | h <;> simp [pattern,local2,Nat.add_mod,h]

theorem current_bulk (b : Bool) (n d : Nat) (h0 : 35≤d) (h1 : d≤34+span b n) :
    zrow (predecessor b n) 2 d=b := by
  obtain ⟨k,hk⟩ : ∃ k,d=k+2 := ⟨d-2,by omega⟩
  subst d
  rw [two_local (predecessor_wall b n)]
  rw [predecessor_bulk b n k (by omega) (by omega),
    predecessor_bulk b n (k+1) (by omega) (by omega),
    predecessor_bulk b n (k+2) (by omega) (by omega),
    predecessor_bulk b n (k+3) (by omega) (by omega),
    predecessor_bulk b n (k+4) (by omega) (by omega)]
  exact local_pattern b k

theorem predecessor_shift (b : Bool) (n i : Nat) (hi : 33≤i) :
    predecessor b n (i+span b n)=predecessor b 0 i := by
  by_cases h36 : i≤36
  · rw [predecessor_bulk b n (i+span b n) (by omega) (by omega),pattern_shift]
    rw [predecessor_bulk b 0 i hi (by rw [span_zero];omega)]
  · have hleft : ¬ i+span b n≤36 := by omega
    have hmid : ¬ i+span b n≤36+span b n := by omega
    simp only [predecessor,span_zero,Nat.add_zero,hleft,hmid,h36,↓reduceIte,
      Nat.add_right_cancel_iff]

theorem current_shift (b : Bool) (n k : Nat) (hk : 33≤k) :
    zrow (predecessor b n) 2 (k+2+span b n)=zrow (predecessor b 0) 2 (k+2) := by
  rw [show k+2+span b n=(k+span b n)+2 by omega,
    two_local (predecessor_wall b n),two_local (predecessor_wall b 0)]
  have h (j : Nat) (hj : j≤4) :
      predecessor b n (k+span b n+j)=predecessor b 0 (k+j) := by
    rw [show k+span b n+j=(k+j)+span b n by omega]
    exact predecessor_shift b n (k+j) (by omega)
  rw [show k+span b n=k+span b n+0 by omega,h 0 (by omega),
    h 1 (by omega),h 2 (by omega),h 3 (by omega),h 4 (by omega)]
  rfl

def frontWord (b : Bool) : List Bool := (next (base b++[true])).take 34
def backWord (b : Bool) : List Bool := (next (base b++[true])).drop 34
def currentWord (b : Bool) (n : Nat) : List Bool :=
  frontWord b++List.replicate (span b n) b++backWord b

theorem prefix_suffix (b : Bool) : frontWord b++backWord b=next (base b++[true]) :=
  List.take_append_drop 34 _

theorem prefix_length (b : Bool) : (frontWord b).length=34 := by
  simp [frontWord,Rule30FiniteLeftWordResearch.length_next,base_length]

theorem suffix_length (b : Bool) : (backWord b).length=5 := by
  simp [backWord,Rule30FiniteLeftWordResearch.length_next,base_length]

theorem predecessor_zero_row (b : Bool) : predecessor b 0=row (base b++[true]) := by
  funext d
  cases d with
  | zero => rfl
  | succ i =>
    by_cases hi : i<36
    · rw [predecessor,ite_eq_left (by omega)]
      exact (row_append_prefix (base b) [true] (i+1) (by rw [base_length];omega)).symm
    · have h0 : ¬ i+1≤36 := by omega
      simp only [predecessor,h0,↓reduceIte,span_zero,Nat.add_zero]
      change decide (i+1=37)=(base b++[true]).getD i false
      rw [getD_append_right _ _ i (by rw [base_length];omega),base_length]
      by_cases he : i=36
      · subst i;rfl
      · rw [Rule30FiniteLeftWordResearch.getD_large [true] (i-36) (by simp;omega)]
        simp [show i+1≠37 by omega]

theorem current_zero (b : Bool) : row (frontWord b++backWord b)=zrow (predecessor b 0) 2 := by
  rw [prefix_suffix,Rule30FiniteLeftWordResearch.row_next,predecessor_zero_row]

theorem current_prefix (b : Bool) (n d : Nat) (hd : d≤34) :
    zrow (predecessor b n) 2 d=zrow (predecessor b 0) 2 d := by
  apply zrow_prefix 36 (t:=2) (d:=d) (h:=?_) (by omega)
  intro i hi
  simp only [predecessor,hi,↓reduceIte]

theorem current_physical (b : Bool) (n : Nat) : row (currentWord b n)=zrow (predecessor b n) 2 := by
  funext d
  by_cases h0 : d≤34
  · calc
      row (currentWord b n) d=row (frontWord b) d := by
        unfold currentWord
        rw [List.append_assoc,row_append_prefix _ _ d (by rw [prefix_length];omega)]
      _=row (frontWord b++backWord b) d := (row_append_prefix _ _ d (by rw [prefix_length];omega)).symm
      _=zrow (predecessor b 0) 2 d := congrFun (current_zero b) d
      _=zrow (predecessor b n) 2 d := (current_prefix b n d h0).symm
  · by_cases h1 : d≤34+span b n
    · rw [current_bulk b n d (by omega) h1]
      exact row_middle _ _ b _ d (by rw [prefix_length];omega) (by rw [prefix_length];omega)
    · have htail : row (currentWord b n) d=row (frontWord b++backWord b) (d-span b n) :=
        row_tail_shift _ _ b _ d (by rw [prefix_length];omega)
      rw [htail,current_zero]
      let k:=d-span b n-2
      have hk : 33≤k := by dsimp only [k];omega
      have h:=current_shift b n k hk
      have hleft : k+2+span b n=d := by dsimp only [k];omega
      have hright : k+2=d-span b n := by dsimp only [k];omega
      rw [hleft,hright] at h
      exact h.symm

theorem predecessor_finite (b : Bool) (n : Nat) : FinSupp (predecessor b n) := by
  refine ⟨37+span b n,fun d hd=>?_⟩
  simp [predecessor,show ¬ d≤36 by omega,show ¬ d≤36+span b n by omega,
    show d≠37+span b n by omega]

theorem predecessor_head (b : Bool) (n : Nat) : predecessor b n 1=true := by
  change row (base b) 1=true
  cases b <;> decide +kernel

theorem predecessor_free (b : Bool) (n : Nat) : zrow (predecessor b n) 1 1=true := by
  have hp : ∀ d,d≤2 → predecessor b n d=predecessor b 0 d := by
    intro d hd
    simp only [predecessor,show d≤36 by omega,↓reduceIte]
  rw [zrow_prefix 2 hp 1 1 (by omega)]
  cases b <;> decide +kernel

theorem front_left (b : Bool) : ∀ d,d≤30 → row (frontWord b) d=left d := by
  cases b <;> decide +kernel

theorem word_left (b : Bool) (n d : Nat) (hd : d≤30) :
    row (currentWord b n) d=left d := by
  unfold currentWord
  rw [List.append_assoc,row_append_prefix _ _ d (by rw [prefix_length];omega)]
  exact front_left b d hd

theorem current_safe (b : Bool) (n : Nat) :
    Rule30VacuumPrefixRankObstructionResearch.Safe13 (currentWord b n) 0 := by
  have hp:=zrow_prefix 30 (word_left b n)
  constructor
  · intro i hi
    rw [hp (2*i) 1 (by omega)]
    exact Rule30CriticalChargeOneCoreResearch.left_inX i
  · intro i hi
    rw [hp (2*i+1) 1 (by omega)]
    simpa only [Nat.add_zero] using Rule30CriticalChargeOneCoreResearch.left_free i

theorem current_canonical (b : Bool) (n : Nat) : Rule30FiniteLeftWordResearch.Canonical (currentWord b n) := by
  constructor
  · cases b <;> rfl
  · unfold currentWord
    simp only [List.reverse_append]
    cases b <;> rfl

open Rule30VacuumPrefixRankObstructionResearch (transition reader_absorbing)
open Rule30WeightedWordPumpResearch (run score scale score_append run_absorbing no_bounded_strict_descent)

theorem reader_front (b : Bool) : run transition 0 (frontWord b)=1 := by
  cases b <;> decide +kernel

theorem unit_scale (n : Nat) : scale 1 n=1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [scale,ih]

theorem score_replicate (C : Nat → Bool → Int) (b : Bool) (n : Nat) :
    score transition C 1 1 (List.replicate n b)=(n:Int)*C 1 b := by
  induction n with
  | zero => simp [score]
  | succ n ih =>
    rw [List.replicate_succ,score,reader_absorbing,ih]
    rw [show ((n+1:Nat):Int)=(n:Int)+1 by omega,Int.add_mul]
    simp
    omega

theorem score_current (C : Nat → Bool → Int) (b : Bool) (n : Nat) :
    score transition C 1 0 (currentWord b n)=
      score transition C 1 0 (frontWord b)+(span b n:Int)*C 1 b+
        score transition C 1 1 (backWord b) := by
  rw [currentWord,List.append_assoc,score_append,reader_front,unit_scale,Int.one_mul,
    score_append,run_absorbing transition 1 reader_absorbing,unit_scale,Int.one_mul,
    score_replicate]
  omega

def HasPastOne (w : List Bool) : Prop := ∃ P : Nat → Bool,
  FinSupp P ∧ P 1=true ∧ zrow P 1 1=true ∧ row w=zrow P 2

theorem current_has_past (b : Bool) (n : Nat) : HasPastOne (currentWord b n) :=
  ⟨predecessor b n,predecessor_finite b n,predecessor_head b n,predecessor_free b n,current_physical b n⟩

theorem span_step (b : Bool) (n : Nat) :
    (span b (n+1):Int)=(span b n:Int)+(if b then 3 else 1) := by
  cases b <;> simp only [span,Bool.false_eq_true,↓reduceIte] <;> omega

theorem sink_cost_nonnegative (C : Nat → Bool → Int) (H B : Int)
    (hb : ∀ w,Rule30FiniteLeftWordResearch.Canonical w →
      Rule30VacuumPrefixRankObstructionResearch.Safe13 w 0 → HasPastOne w →
      B≤H+score transition C 1 0 w) (b : Bool) : 0≤C 1 b := by
  apply Classical.byContradiction
  intro hn
  have hc : C 1 b≤-1 := by omega
  apply no_bounded_strict_descent (fun n=>score transition C 1 0 (currentWord b n)) (B-H)
  · intro n
    have h:=hb _ (current_canonical b n) (current_safe b n) (current_has_past b n)
    omega
  · intro n
    rw [score_current,score_current,span_step,Int.add_mul]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] at * <;> omega

end Rule30FiniteImagePumpResearch
