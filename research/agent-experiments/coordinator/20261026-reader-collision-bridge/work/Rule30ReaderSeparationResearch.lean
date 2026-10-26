module
public import Rule30ColumnReaderResearch

/-! The reader's entire state is a period-two factor of the triangular
update. Outside its invariant sink, two current bits decide trace equality.
Separation inside the sink remains OPEN; no full completeness is asserted. -/
@[expose] public section
namespace Rule30ReaderSeparationResearch
open Rule30ColumnReaderResearch
open Rule30CommonPastResearch (Actual)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def phase (q : Nat) : Nat :=
  ([0,1,2,3,5,4,7,6,10,11,8,9,12,14,13,15,16].getD q 15)

def forced (q : Nat) : Bool :=
  q==1 || q==2 || q==5 || q==6 || q==9 || q==10 || q==13 || q==14

def Facts (q : Coupled) : Prop :=
  q.transformed=phase q.raw ∧ q.raw<17 ∧
  (q.raw≠15 → q.previous.1=q.previous.2 → accepted q.raw=false →
    forced (phase q.raw)=true) ∧
  (forced q.raw=true → q.previous.1≠q.previous.2)

instance (q : Coupled) : Decidable (Facts q) := by unfold Facts;infer_instance

theorem facts_check : allowed.all (fun q => decide (Facts q))=true := by decide +kernel

theorem facts (q : Coupled) (hq : q∈allowed) : Facts q :=
  of_decide_eq_true (List.all_eq_true.mp facts_check q hq)

theorem phase_check : (List.range 17).all (fun q =>
    decide (phase (phase q)=q ∧ (phase q=15 ↔ q=15)))=true := by decide +kernel

theorem phase_facts (q : Nat) (hq : q<17) :
    phase (phase q)=q ∧ (phase q=15 ↔ q=15) :=
  of_decide_eq_true (List.all_eq_true.mp phase_check q (List.mem_range.mpr hq))

theorem run_lt (ss : List Symbol) : run 0 ss<17 := by
  have h := (facts _ (run_mem ss initial initial_mem)).2.1
  simpa only [raw_run,initial] using h

theorem state_step (ss : List Symbol) : run 0 (stepWord ss)=phase (run 0 ss) := by
  have h := (facts _ (run_mem ss initial initial_mem)).1
  simpa only [raw_run,transformed_run,initial,stepWord] using h

theorem state_period_two (ss : List Symbol) :
    run 0 (stepWord (stepWord ss))=run 0 ss := by
  rw [state_step,state_step]
  exact (phase_facts _ (run_lt ss)).1

theorem sink_step_iff (ss : List Symbol) :
    run 0 (stepWord ss)=15 ↔ run 0 ss=15 := by
  rw [state_step]
  exact (phase_facts _ (run_lt ss)).2

theorem nonsink_word (ss : List Symbol) (hn : run 0 ss≠15)
    (h0 : (lastPair zero ss).1=(lastPair zero ss).2)
    (h1 : (lastPair zero (stepWord ss)).1=(lastPair zero (stepWord ss)).2) :
    accepted (run 0 ss)=true := by
  have f0 := facts _ (run_mem ss initial initial_mem)
  have f1 := facts _ (run_mem (stepWord ss) initial initial_mem)
  cases he : accepted (run 0 ss) with
  | true => rfl
  | false =>
      have hf := f0.2.2.1
      simp only [raw_run,previous_run,initial] at hf
      have hforce := hf hn h0 he
      have hneq := f1.2.2.2
      simp only [raw_run,previous_run,initial] at hneq
      rw [state_step] at hneq
      exact False.elim (hneq hforce h1)

theorem reader_complete_outside_sink (a b : Nat → Nat → Bool)
    (ha : Actual a) (hb : Actual b) (n : Nat) (hn : 0<n)
    (hs : run 0 (takeRow (fun j => (a 0 j,b 0 j)) n)≠15) :
    accepted (run 0 (takeRow (fun j => (a 0 j,b 0 j)) n))=true ↔
      ∀ t, a t (n-1)=b t (n-1) := by
  constructor
  · exact reader_sound a b ha hb n hn
  · intro he
    apply nonsink_word _ hs
    · simpa only [last_take n hn] using he 0
    · rw [prefix_step a b ha hb 0 n]
      simpa only [last_take n hn] using he 1

theorem sink_time_iff (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (n t : Nat) :
    run 0 (takeRow (fun j => (a t j,b t j)) n)=15 ↔
      run 0 (takeRow (fun j => (a 0 j,b 0 j)) n)=15 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [← prefix_step a b ha hb t n]
      exact (sink_step_iff _).trans ih

theorem nonsink_two_times (a b : Nat → Nat → Bool)
    (ha : Actual a) (hb : Actual b) (n : Nat) (hn : 0<n)
    (hs : run 0 (takeRow (fun j => (a 0 j,b 0 j)) n)≠15)
    (h0 : a 0 (n-1)=b 0 (n-1)) (h1 : a 1 (n-1)=b 1 (n-1)) :
    ∀ t, a t (n-1)=b t (n-1) := by
  apply reader_sound a b ha hb n hn
  apply nonsink_word _ hs
  · simpa only [last_take n hn] using h0
  · rw [prefix_step a b ha hb 0 n]
    simpa only [last_take n hn] using h1

end Rule30ReaderSeparationResearch
