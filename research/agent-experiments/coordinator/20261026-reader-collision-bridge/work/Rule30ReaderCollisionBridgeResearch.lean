module
public import Rule30ReaderSeparationResearch
public import Rule30FrontReductionResearch

/-! The sound reader's accepted prefixes satisfy the collision-clock condition.
Consequently, separation in the remaining sink would also give the background
clock hypothesis and initial-subset preservation. Sink separation itself and
the fixed-center bridge to Problem 1 remain open. -/
@[expose] public section
namespace Rule30ReaderCollisionBridgeResearch
open Rule30ColumnReaderResearch
open Rule30ReaderSeparationResearch
open Rule30CommonPastResearch
open Rule30FrontReductionResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def pref (a b : Nat → Nat → Bool) (t n : Nat) : Coupled :=
  runCoupled initial (takeRow (fun j => (a t j,b t j)) n)

theorem take_snoc (x : Nat → Symbol) (n : Nat) :
    takeRow x (n+1)=takeRow x n ++ [x n] := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change x 0 :: takeRow (fun j => x (j+1)) (n+1)=
      (x 0 :: takeRow (fun j => x (j+1)) n) ++ [x (n+1)]
    rw [ih]
    rfl

theorem coupled_append (xs ys : List Symbol) (q : Coupled) :
    runCoupled q (xs++ys)=runCoupled (runCoupled q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons x xs ih => exact ih (advance q x)

theorem pref_snoc (a b : Nat → Nat → Bool) (t n : Nat) :
    pref a b t (n+1)=advance (pref a b t n) (a t n,b t n) := by
  unfold pref
  rw [take_snoc,coupled_append]
  rfl

theorem pref_mem (a b : Nat → Nat → Bool) (t n : Nat) : pref a b t n∈allowed :=
  run_mem _ initial initial_mem

theorem pref_raw (a b : Nat → Nat → Bool) (t n : Nat) :
    (pref a b t n).raw=run 0 (takeRow (fun j => (a t j,b t j)) n) := by
  exact raw_run _ initial

theorem pref_previous (a b : Nat → Nat → Bool) (t n : Nat) :
    (pref a b t (n+1)).previous=(a t n,b t n) := by
  rw [pref_snoc]
  rfl

theorem pref_older (a b : Nat → Nat → Bool) (t n : Nat) :
    (pref a b t (n+2)).older=(a t n,b t n) := by
  rw [show n+2=(n+1)+1 by omega,pref_snoc]
  exact pref_previous a b t n

theorem raw_step (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b) (t n : Nat) :
    (pref a b (t+1) n).raw=phase (pref a b t n).raw := by
  simp only [pref_raw]
  rw [← prefix_step a b ha hb t n,state_step]

theorem raw_two (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b) (t n : Nat) :
    (pref a b (t+2) n).raw=(pref a b t n).raw := by
  rw [show t+2=(t+1)+1 by omega,raw_step a b ha hb,raw_step a b ha hb]
  exact (phase_facts _ (by rw [pref_raw];exact run_lt _)).1

theorem accepted_fixed_check : (List.range 17).all (fun q =>
    decide (accepted q=true → phase q=q))=true := by decide +kernel

theorem accepted_fixed (q : Nat) (hq : q<17) (he : accepted q=true) : phase q=q :=
  (of_decide_eq_true (List.all_eq_true.mp accepted_fixed_check q (List.mem_range.mpr hq))) he

theorem raw_fixed (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b) (n : Nat)
    (he : accepted (pref a b 0 n).raw=true) : ∀ t, (pref a b t n).raw=(pref a b 0 n).raw := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [raw_step a b ha hb,ih]
    exact accepted_fixed _ (by rw [pref_raw];exact run_lt _) he

def diffTag (q : Nat) : Bool := q==6 || q==9 || q==13 || q==14

def Non16Fact (q : Coupled) : Prop := accepted q.raw=true → q.raw≠16 →
  (q.previous.1 || q.older.1)=(q.previous.2 || q.older.2)

def SixteenPreFact (q : Coupled) : Prop := ∀ x y : Bool, next q.raw (x,y)=16 →
  (q.previous.1 || q.older.1)=true ∧ (q.previous.2 || q.older.2)=true ∧
    xor q.previous.1 q.previous.2=diffTag q.raw

instance (q : Coupled) : Decidable (Non16Fact q) := by unfold Non16Fact;infer_instance
instance (q : Coupled) : Decidable (SixteenPreFact q) := by unfold SixteenPreFact;infer_instance

theorem non16_check : allowed.all (fun q => decide (Non16Fact q))=true := by decide +kernel
theorem sixteen_check : allowed.all (fun q => decide (SixteenPreFact q))=true := by decide +kernel

theorem non16_fact (q : Coupled) (hq : q∈allowed) : Non16Fact q :=
  of_decide_eq_true (List.all_eq_true.mp non16_check q hq)
theorem sixteen_fact (q : Coupled) (hq : q∈allowed) : SixteenPreFact q :=
  of_decide_eq_true (List.all_eq_true.mp sixteen_check q hq)

theorem xor_cancel : ∀ x y z : Bool, xor (xor x z) (xor y z)=xor x y := by decide +kernel
theorem xor_true : ∀ x : Bool, xor x true=(!x) := by decide +kernel
theorem xor_false_eq : ∀ x y : Bool, xor x y=false → x=y := by decide +kernel

/-- Every accepted state other than 16 permanently shields the next difference. -/
theorem non16_permanent (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b) (n : Nat)
    (he : accepted (pref a b 0 (n+2)).raw=true) (hn : (pref a b 0 (n+2)).raw≠16) :
    ∀ t, delta a b t (n+2)=delta a b 0 (n+2) := by
  have hh (t : Nat) : (a t (n+1) || a t n)=(b t (n+1) || b t n) := by
    have f := non16_fact _ (pref_mem a b t (n+2))
    have hf := raw_fixed a b ha hb (n+2) he t
    have h := f (by rw [hf];exact he) (by rw [hf];exact hn)
    simpa only [pref_previous,pref_older] using h
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    change xor (a (t+1) (n+2)) (b (t+1) (n+2))=delta a b 0 (n+2)
    rw [ha t (n+2),hb t (n+2)]
    simp only [march]
    rw [hh t,xor_cancel]
    exact ih

theorem drive_from_pref (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b) (t n : Nat) :
    a (t+1) (n+1)=xor (a t (n+1)) ((pref a b t (n+1)).previous.1 || (pref a b t (n+1)).older.1) ∧
    b (t+1) (n+1)=xor (b t (n+1)) ((pref a b t (n+1)).previous.2 || (pref a b t (n+1)).older.2) := by
  cases n with
  | zero => simp [ha t 1,hb t 1,march,pref,takeRow,runCoupled,initial,advance,zero]
  | succ n =>
    rw [show n+1+1=n+2 by omega,pref_previous,pref_older,ha t (n+2),hb t (n+2)]
    exact ⟨rfl,rfl⟩

/-- State 16 supplies exactly the alternating shared clock and two-step difference. -/
theorem sixteen_clock (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b) (n : Nat)
    (hs : (pref a b 0 (n+2)).raw=16) :
    (∀ t, a (t+1) (n+1)=!a t (n+1)) ∧
      (∀ t, delta a b (t+2) n=delta a b t n) := by
  have he : accepted (pref a b 0 (n+2)).raw=true := by rw [hs];decide
  have ht (t : Nat) : (pref a b t (n+2)).raw=16 := (raw_fixed a b ha hb (n+2) he t).trans hs
  have hpre (t : Nat) : SixteenPreFact (pref a b t (n+1)) := sixteen_fact _ (pref_mem a b t (n+1))
  have hnext (t : Nat) : next (pref a b t (n+1)).raw (a t (n+1),b t (n+1))=16 := by
    have h := ht t
    rw [show n+2=(n+1)+1 by omega,pref_snoc] at h
    exact h
  have f (t : Nat) := hpre t (a t (n+1)) (b t (n+1)) (hnext t)
  constructor
  · intro t
    rw [(drive_from_pref a b ha hb t n).1,(f t).1,xor_true]
  · intro t
    have g (s : Nat) : delta a b s n=diffTag (pref a b s (n+1)).raw := by
      simpa only [pref_previous,delta] using (f s).2.2
    rw [g (t+2),g t,raw_two a b ha hb]

theorem accepted_collision_clock (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b) (n : Nat)
    (he : accepted (pref a b 0 (n+2)).raw=true) (hi : delta a b 0 (n+2)=true) :
    (∀ t, delta a b t (n+2)=true) ∨
      ((∀ t, a (t+1) (n+1)=!a t (n+1)) ∧ (∀ t, delta a b (t+2) n=delta a b t n)) := by
  by_cases hs : (pref a b 0 (n+2)).raw=16
  · exact Or.inr (sixteen_clock a b ha hb n hs)
  · exact Or.inl (fun t => (non16_permanent a b ha hb n he hs t).trans hi)

def SinkSeparates (a b : Nat → Nat → Bool) : Prop := ∀ n, 0<n →
  run 0 (takeRow (fun j => (a 0 j,b 0 j)) n)=15 → ∃ t, a t (n-1)≠b t (n-1)

theorem reader_exact_of_sink_separation (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (hsep : SinkSeparates a b) (n : Nat) (hn : 0<n) :
    accepted (run 0 (takeRow (fun j => (a 0 j,b 0 j)) n))=true ↔
      ∀ t, a t (n-1)=b t (n-1) := by
  constructor
  · exact reader_sound a b ha hb n hn
  · intro he
    have hs : run 0 (takeRow (fun j => (a 0 j,b 0 j)) n)≠15 := by
      intro hs
      obtain ⟨t,ht⟩ := hsep n hn hs
      exact ht (he t)
    exact (reader_complete_outside_sink a b ha hb n hn hs).mpr he

/-- Sink separation would discharge the formerly separate background clock gap. -/
theorem collision_clock_of_sink_separation (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (hsep : SinkSeparates a b) : CollisionClock a b := by
  intro n he hi
  have htrace (t : Nat) : a t (n+1)=b t (n+1) := xor_false_eq _ _ (he t)
  have hs : run 0 (takeRow (fun j => (a 0 j,b 0 j)) (n+2))≠15 := by
    intro hs
    obtain ⟨t,ht⟩ := hsep (n+2) (by omega) hs
    apply ht
    simpa using htrace t
  have hr := (reader_complete_outside_sink a b ha hb (n+2) (by omega) hs).mpr (by simpa using htrace)
  exact accepted_collision_clock a b ha hb n (by simpa only [pref_raw] using hr) hi

theorem front_of_sink_separation (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (hsep : SinkSeparates a b) : FrontStable a b :=
  front_of_collision_clock a b ha hb (collision_clock_of_sink_separation a b ha hb hsep)

theorem preservation_of_sink_separation (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (hfin : Finite (delta a b 0)) (hsep : SinkSeparates a b) : Preserves a b :=
  preservation_of_collision_clock a b ha hb hfin (collision_clock_of_sink_separation a b ha hb hsep)

end Rule30ReaderCollisionBridgeResearch
