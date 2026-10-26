import CedarWhiteTransport

namespace CedarZeroFront
open CedarSafetySoundness CedarSafety CedarWhiteTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def front : List Bool :=
  [false,false,true,true,false,true,false,false,false,true,true,true,
   false,false,true,true,false,true,true,true,true,false,true,true]
def core (k : Nat) : List Bool := front ++ List.replicate k false ++ [true]
def block : List Bool := front ++ List.replicate 8 false

/-- The known 32-cell block has a quiet older boundary for the appended
tail during four steps; direct reduction proves this for EVERY tail. -/
theorem block_transport (xs : List Bool) :
    (evolution 4 (block ++ xs)).drop 8 = front ++ evolution 4 xs := by rfl

theorem evolution_singleton (t : Nat) : evolution t [true] = [true] := by
  induction t with
  | zero => rfl
  | succ t ih => rw [evolution,ih]; rfl

theorem stationary_terminal (k t : Nat) :
    evolution t (List.replicate k false ++ [true]) = List.replicate k false ++ [true] := by
  induction k with
  | zero => simpa using evolution_singleton t
  | succ k ih => simpa only [List.replicate_succ,List.cons_append,evolution_false_cons] using congrArg (List.cons false) ih

theorem core_step (k : Nat) : (evolution 4 (core (k+8))).drop 8 = core k := by
  have hsplit : core (k+8) = block ++ (List.replicate k false ++ [true]) := by
    simp only [core,block,show k+8=8+k by omega,← List.replicate_append_replicate,List.append_assoc]
  rw [hsplit,block_transport,stationary_terminal]
  rfl

/-- Retain the actual evolved prefix; it is never replaced by a white boundary. -/
theorem rank_step (older : List Bool) (k : Nat) :
    ∃ nextOlder : List Bool, evolution 4 (older ++ core (k+8)) = nextOlder ++ core k := by
  have h := prefix_transport older (core (k+8)) 4
  change (evolution 4 (older ++ core (k+8))).drop (older.length+8) =
    (evolution 4 (core (k+8))).drop 8 at h
  rw [core_step] at h
  refine ⟨(evolution 4 (older ++ core (k+8))).take (older.length+8),?_⟩
  have e := List.take_append_drop (older.length+8) (evolution 4 (older ++ core (k+8)))
  rw [h] at e
  exact e.symm

theorem length_change (p r : Bool) (xs : List Bool) : (change p r xs).length = xs.length := by
  induction xs generalizing p r with
  | nil => rfl
  | cons v vs ih => simp [change,ih]

theorem length_evolution (xs : List Bool) (t : Nat) : (evolution t xs).length = xs.length := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [evolution,F,length_change] using ih

theorem newest_drop (xs : List Bool) (n : Nat) (h : n < xs.length) : newest (xs.drop n) = newest xs := by
  simp only [newest,List.getLastD_eq_getLast?,List.getLast?_drop,if_neg (by omega : ¬ xs.length ≤ n)]

theorem newest_prefix_cone (older xs : List Bool) (t : Nat) (h : 2*t < xs.length) :
    newest (evolution t (older++xs)) = newest (evolution t xs) := by
  have e := congrArg newest (prefix_transport older xs t)
  rw [newest_drop _ _ (by rw [length_evolution,List.length_append]; omega),
      newest_drop _ _ (by rw [length_evolution]; exact h)] at e
  exact e

def escape (k : Fin 8) : Nat :=
  match k.val with
  | 0 => 1
  | 1 => 3
  | 2 => 12
  | 3 => 7
  | 4 => 3
  | 5 => 5
  | 6 => 8
  | _ => 10

def traceRow (k : Fin 8) (t : Nat) : List Bool :=
  match k.val,t with
  | 0,0 => [false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true]
  | 0,1 => [false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,true,false,false,false]
  | 0,2 => [false,false,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,true,false]
  | 1,0 => [false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,false,true,true,false,true]
  | 1,1 => [false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,true,false,false,true,false]
  | 1,2 => [false,false,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,true,true,true]
  | 1,3 => [false,false,true,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,true,false,false,false,false]
  | 1,4 => [false,false,true,true,false,true,false,false,false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,false]
  | 2,0 => [false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,false,true,true,false,false,true]
  | 2,1 => [false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,true,false,false,true,true,true]
  | 2,2 => [false,false,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,true,true,false,false]
  | 2,3 => [false,false,true,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true,true]
  | 2,4 => [false,false,true,true,false,true,false,false,false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,false]
  | 2,5 => [false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,true]
  | 2,6 => [false,false,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,false]
  | 2,7 => [false,false,true,false,true,false,true,true,true,false,false,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,true]
  | 2,8 => [false,false,true,true,false,true,false,false,false,true,true,false,true,true,false,false,false,false,true,true,false,true,false,false,false,true,false]
  | 2,9 => [false,false,true,false,true,false,true,true,false,true,false,true,false,false,true,true,false,false,true,false,true,false,true,true,false,true,true]
  | 2,10 => [false,false,true,true,false,true,false,false,true,false,true,false,true,true,true,false,true,true,true,true,false,true,false,false,true,false,false]
  | 2,11 => [false,false,true,false,true,false,true,true,true,true,false,true,false,false,false,true,false,false,false,false,true,false,true,true,true,true,true]
  | 2,12 => [false,false,true,true,false,true,false,false,false,false,true,false,true,true,false,true,true,true,false,false,true,true,false,false,false,false,false]
  | 2,13 => [false,false,true,false,true,false,true,true,false,false,true,true,false,false,true,false,false,false,true,true,true,false,true,true,false,false,false]
  | 3,0 => [false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,false,true,true,false,false,false,true]
  | 3,1 => [false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,true,false,false,true,true,false,true]
  | 3,2 => [false,false,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,true,true,false,true,false]
  | 3,3 => [false,false,true,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true,false,true]
  | 3,4 => [false,false,true,true,false,true,false,false,false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,false]
  | 3,5 => [false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,true]
  | 3,6 => [false,false,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,true]
  | 3,7 => [false,false,true,false,true,false,true,true,true,false,false,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,false,false]
  | 3,8 => [false,false,true,true,false,true,false,false,false,true,true,false,true,true,false,false,false,false,true,true,false,true,false,false,false,true,true,false]
  | 4,0 => [false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,false,true,true,false,false,false,false,true]
  | 4,1 => [false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,true,false,false,true,true,false,false,true]
  | 4,2 => [false,false,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,true,true,false,true,true,true]
  | 4,3 => [false,false,true,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true,false,false,false]
  | 4,4 => [false,false,true,true,false,true,false,false,false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,false]
  | 5,0 => [false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,false,true,true,false,false,false,false,false,true]
  | 5,1 => [false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,true,false,false,true,true,false,false,false,true]
  | 5,2 => [false,false,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,true,true,false,true,true,false,true]
  | 5,3 => [false,false,true,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true,false,false,true,false]
  | 5,4 => [false,false,true,true,false,true,false,false,false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,true]
  | 5,5 => [false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,false]
  | 5,6 => [false,false,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,false]
  | 6,0 => [false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,false,true,true,false,false,false,false,false,false,true]
  | 6,1 => [false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,true,false,false,true,true,false,false,false,false,true]
  | 6,2 => [false,false,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,true,true,false,true,true,false,false,true]
  | 6,3 => [false,false,true,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true,false,false,true,true,true]
  | 6,4 => [false,false,true,true,false,true,false,false,false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,false,false]
  | 6,5 => [false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,true,true]
  | 6,6 => [false,false,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,true,false]
  | 6,7 => [false,false,true,false,true,false,true,true,true,false,false,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,true,true]
  | 6,8 => [false,false,true,true,false,true,false,false,false,true,true,false,true,true,false,false,false,false,true,true,false,true,false,false,false,true,true,true,false,false,false]
  | 6,9 => [false,false,true,false,true,false,true,true,false,true,false,true,false,false,true,true,false,false,true,false,true,false,true,true,false,true,false,false,true,true,false]
  | 7,0 => [false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,true]
  | 7,1 => [false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,true,false,false,true,true,false,false,false,false,false,true]
  | 7,2 => [false,false,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,true,true,false,true,true,false,false,false,true]
  | 7,3 => [false,false,true,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true,false,false,true,true,false,true]
  | 7,4 => [false,false,true,true,false,true,false,false,false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,true,false,true,true,true,true,false,true,false]
  | 7,5 => [false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,false,false,true,false,true]
  | 7,6 => [false,false,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false]
  | 7,7 => [false,false,true,false,true,false,true,true,true,false,false,false,true,false,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,true,false,true]
  | 7,8 => [false,false,true,true,false,true,false,false,false,true,true,false,true,true,false,false,false,false,true,true,false,true,false,false,false,true,true,true,false,false,true,false]
  | 7,9 => [false,false,true,false,true,false,true,true,false,true,false,true,false,false,true,true,false,false,true,false,true,false,true,true,false,true,false,false,true,true,true,true]
  | 7,10 => [false,false,true,true,false,true,false,false,true,false,true,false,true,true,true,false,true,true,true,true,false,true,false,false,true,false,true,true,true,false,false,false]
  | 7,11 => [false,false,true,false,true,false,true,true,true,true,false,true,false,false,false,true,false,false,false,false,true,false,true,true,true,true,false,false,false,true,true,false]
  | _,_ => []

theorem escape_bound : ∀ k : Fin 8, escape k ≤ 12 := by decide
theorem trace_initial : ∀ k : Fin 8, traceRow k 0 = core k.val := by decide
theorem trace_step : ∀ (k : Fin 8) (t : Fin 13), t.val ≤ escape k →
    F (traceRow k t.val) = traceRow k (t.val+1) := by decide
theorem trace_terminal : ∀ k : Fin 8,
    2*(escape k+1) < (core k.val).length ∧
    newest (traceRow k (escape k)) = false ∧
    newest (traceRow k (escape k+1)) = false := by decide

theorem actual_trace (k : Fin 8) (t : Nat) (h : t ≤ escape k+1) :
    evolution t (core k.val) = traceRow k t := by
  induction t with
  | zero => exact (trace_initial k).symm
  | succ t ih =>
    rw [evolution,ih (by omega)]
    have hb := escape_bound k
    exact trace_step k ⟨t,by omega⟩ (by change t ≤ escape k; omega)

theorem terminal_certificate : ∀ k : Fin 8,
    2*(escape k+1) < (core k.val).length ∧
    newest (evolution (escape k) (core k.val)) = false ∧
    newest (evolution (escape k+1) (core k.val)) = false := by
  intro k
  rw [actual_trace k (escape k) (by omega),actual_trace k (escape k+1) (by omega)]
  exact trace_terminal k

theorem terminal_not_safe (older : List Bool) (k : Fin 8) : ¬ Safe (older ++ core k.val) := by
  intro h
  obtain ⟨hm,h0,h1⟩ := terminal_certificate k
  apply h (escape k)
  constructor
  · rw [newest_prefix_cone older (core k.val) (escape k) (by omega)]
    exact h0
  · rw [newest_prefix_cone older (core k.val) (escape k+1) hm]
    exact h1

theorem safe_shift (xs : List Bool) (s : Nat) (h : Safe xs) : Safe (evolution s xs) := by
  intro t
  rw [← evolution_add t s,← evolution_add (t+1) s,
      show t+1+s=(t+s)+1 by omega]
  exact h (t+s)

/-- Uniform exclusion of this one regular suffix family by the decreasing
gap rank. No assertion is made that all unsafe/safe words reach this front. -/
theorem not_safe_zero_front (k : Nat) (older : List Bool) : ¬ Safe (older ++ core k) := by
  induction k using Nat.strongRecOn generalizing older with
  | ind k ih =>
    intro h
    by_cases small : k < 8
    · exact terminal_not_safe older ⟨k,small⟩ h
    · obtain ⟨nextOlder,he⟩ := rank_step older (k-8)
      rw [show k-8+8=k by omega] at he
      have nextSafe := safe_shift (older ++ core k) 4 h
      rw [he] at nextSafe
      exact ih (k-8) (by omega) nextOlder nextSafe

end CedarZeroFront
