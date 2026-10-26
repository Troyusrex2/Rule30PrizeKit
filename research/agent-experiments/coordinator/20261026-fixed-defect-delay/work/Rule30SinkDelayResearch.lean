module
public import Rule30SharedTailDelayResearch
public import Rule30ColumnReaderResearch

/-! The arbitrarily delayed finite examples really start in reader state 15.
This is a delay obstruction, not a counterexample to eventual separation. -/
@[expose] public section
namespace Rule30SinkDelayResearch
open Rule30SharedTailCounterResearch Rule30SharedTailDelayResearch
open Rule30ColumnReaderResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def initialWord (x y : State) (N : Nat) : List Symbol :=
  ((List.range N).map (fun k => (x k,y k))).reverse
def suffix : List Symbol :=
  [(true,true),(false,false),(false,true),(true,false),
   (false,true),(true,false),(false,false)]

theorem common_check : ([0,3,12] : List Nat).all (fun q =>
    decide (∀ b : Bool, next q (b,b)∈([0,3,12] : List Nat)))=true := by decide +kernel
theorem suffix_check : ([0,3,12] : List Nat).all
    (fun q => decide (run q suffix=15))=true := by decide +kernel

theorem run_append (a b : List Symbol) (q : Nat) : run q (a++b)=run (run q a) b := by
  induction a generalizing q with
  | nil => rfl
  | cons s a ih => exact ih (next q s)

theorem run_common (ss : List Symbol) (q : Nat) (hq : q∈([0,3,12] : List Nat))
    (hs : ∀ s∈ss, s.1=s.2) : run q ss∈([0,3,12] : List Nat) := by
  induction ss generalizing q with
  | nil => exact hq
  | cons s ss ih =>
      have he : s.1=s.2 := hs s (by simp)
      have hc := of_decide_eq_true (List.all_eq_true.mp common_check q hq)
      have hn : next q s∈([0,3,12] : List Nat) := by
        cases s with
        | mk a b => change a=b at he;subst b;exact hc a
      exact ih (next q s) hn (fun s h => hs s (by simp [h]))

theorem common_suffix (ss : List Symbol) (hs : ∀ s∈ss, s.1=s.2) :
    run 0 (ss++suffix)=15 := by
  rw [run_append]
  exact of_decide_eq_true (List.all_eq_true.mp suffix_check _ (run_common ss 0 (by simp) hs))

theorem original_word_sink (N : Nat) (hN : 7≤N) :
    run 0 (initialWord (initial true) (initial false) N)=15 := by
  let higher := (List.range (N-7)).map (fun j => (initial true (7+j),initial false (7+j)))
  have hw : initialWord (initial true) (initial false) N=higher.reverse++suffix := by
    unfold initialWord
    rw [show N=7+(N-7) by omega,List.range_add,List.map_append,List.reverse_append,List.map_map]
    rfl
  rw [hw]
  apply common_suffix
  intro s hs
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hs)
  exact shared_tail 0 (7+j) (by omega)

theorem arbitrary_sink_delay (T : Nat) : ∃ x y : State,
    Finite x ∧ Finite y ∧
    (∀ k, 2*T+8≤k → x k=false ∧ y k=false) ∧
    (∀ k, k<5 → x k=initial true k ∧ y k=initial false k) ∧
    run 0 (initialWord x y (2*T+8))=15 ∧
    (∀ t k, 5≤k → orbit x t k=orbit y t k) ∧
    (∀ t, orbit x t 4≠orbit y t 4) ∧
    orbit x 0 5≠orbit x 1 5 ∧
    (∀ t, t≤T → orbit x t 0=orbit y t 0) := by
  obtain ⟨x,y,hx,hy,hbound,ht,hs,hsource,hn,he⟩ := arbitrary_finite_delay T
  have hword : initialWord x y (2*T+8)=initialWord (initial true) (initial false) (2*T+8) := by
    unfold initialWord
    congr 1
    apply List.map_congr_left
    intro k hk
    have hh := hs k (List.mem_range.mp hk)
    rw [hh.1,hh.2]
  have hsmall : ∀ k, k<5 → x k=initial true k ∧ y k=initial false k := by
    intro k hk
    exact hs k (by omega)
  refine ⟨x,y,hx,hy,hbound,hsmall,?_,tail_stays_shared x y 5 ht,hsource,hn,he⟩
  rw [hword]
  exact original_word_sink _ (by omega)

end Rule30SinkDelayResearch
