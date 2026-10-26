import HeightOneTransfer
import Rule30CommonPastResearch

/-! Every genuine finite-white newest trace has a positive even returning
column clock. This transports the existing all-depth triangular periodicity
theorem to the literal finite-list evolution; no clock premise is added. -/
namespace HeightOnePeriodicity
open CedarSafetySoundness CedarSafety HeightOneLogic HeightOneSemantics HeightOneTransfer
open Rule30CommonPastResearch
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def takeBits (x : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n+1 => x 0 :: takeBits (fun j => x (j+1)) n

def rowStep (p r : Bool) (x : Nat → Bool) : Nat → Bool
  | 0 => xor (x 0) (p || r)
  | 1 => xor (x 1) (x 0 || p)
  | j+2 => xor (x (j+2)) (x (j+1) || x j)

theorem row_shift (p r : Bool) (x : Nat → Bool) :
    rowStep (x 0) p (fun j => x (j+1))=(fun j => rowStep p r x (j+1)) := by
  funext j
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl

theorem take_change (p r : Bool) (x : Nat → Bool) (n : Nat) :
    change p r (takeBits x n)=takeBits (rowStep p r x) n := by
  induction n generalizing p r x with
  | zero => rfl
  | succ n ih =>
      simp only [takeBits,change]
      rw [ih,row_shift]
      rfl

theorem row_white (x : Nat → Bool) : rowStep false false x=march x := by
  funext j
  cases j with
  | zero => simp only [rowStep,march]; cases x 0 <;> rfl
  | succ j =>
      cases j with
      | zero => simp only [rowStep,march]; cases x 0 <;> cases x 1 <;> rfl
      | succ j => rfl

theorem take_white (x : Nat → Bool) (n : Nat) :
    F (takeBits x n)=takeBits (march x) n := by
  rw [F,take_change,row_white]

theorem take_initial (xs : List Bool) : takeBits (fun j => xs.getD j false) xs.length=xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
      change v :: takeBits (fun j => vs.getD j false) vs.length=v::vs
      rw [ih]

theorem take_last (x : Nat → Bool) (n : Nat) (d : Bool) :
    (takeBits x (n+1)).getLastD d=x n := by
  induction n generalizing x d with
  | zero => rfl
  | succ n ih =>
      rw [takeBits,List.getLastD_cons]
      exact ih (fun j => x (j+1)) (x 0)

theorem take_newest (x : Nat → Bool) (n : Nat) (hn : 0<n) :
    newest (takeBits x n)=x (n-1) := by
  cases n with
  | zero => omega
  | succ n => exact take_last x n false

def full (xs : List Bool) : Nat → Nat → Bool
  | 0 => fun j => xs.getD j false
  | t+1 => march (full xs t)

theorem full_actual (xs : List Bool) : Actual (full xs) := fun _ _ => rfl

theorem prefix_full (xs : List Bool) (t : Nat) :
    takeBits (full xs t) xs.length=evolution t xs := by
  induction t with
  | zero => exact take_initial xs
  | succ t ih =>
      change takeBits (march (full xs t)) xs.length=F (evolution t xs)
      rw [← take_white,ih]

theorem trace_full (xs : List Bool) (hn : 0<xs.length) (t : Nat) :
    tr xs t=full xs t (xs.length-1) := by
  rw [trace_eq,← prefix_full,take_newest _ _ hn]

theorem exists_even_column_period (xs : List Bool) :
    ∃ P : Nat, 0<P ∧ Even P ∧ Periodic (tr xs) P := by
  by_cases hn : 0<xs.length
  · let L := 2^(xs.length-1)
    have hL : 0<L := Nat.pow_pos (by decide)
    have hp := actual_periodic (full xs) (full_actual xs) (xs.length-1)
    refine ⟨2*L,by omega,⟨L,by omega⟩,?_⟩
    intro t
    rw [trace_full xs hn,trace_full xs hn]
    change full xs (t+2*L) (xs.length-1)=full xs t (xs.length-1)
    rw [show t+2*L=(t+L)+L by omega]
    exact (hp (t+L)).trans (hp t)
  · have hx : xs=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    refine ⟨2,by decide,by decide,?_⟩
    intro t
    change RootShortExtensionCore.lift8 zero (t+2)=RootShortExtensionCore.lift8 zero t
    rw [RootShortExtensionCore.lift8_zero,RootShortExtensionCore.lift8_zero]

theorem closed_of_alltime_span (b : Nat → Bool) (P : Nat)
    (he : Even P) (hp : Periodic b P) (hs : SpanOne b) : WH b P=0 := by
  obtain ⟨lo,hl⟩ := hs
  have h0 := hl 0
  have h2 := hl (P+P)
  have hzero : WH b 0=0 := RootEventHeight.height_zero _
  have hsum := height_shift_period b P he hp P
  rw [hzero] at h0
  omega

/-- The all-time height theorem needs no supplied temporal clock. -/
theorem alltime_height_one_shorter_counterexample (xs : List Bool)
    (hs : SpanOne (tr xs)) (hn : ¬ Periodic (tr xs) 4) :
    ∃ ys : List Bool, ys.length+1=xs.length ∧ CedarSafety.Safe ys ∧ evolution 8 ys≠ys := by
  obtain ⟨P,hP,he,hp⟩ := exists_even_column_period xs
  apply height_one_shorter_counterexample xs P hP he hp (closed_of_alltime_span _ _ he hp hs)
  · obtain ⟨lo,hl⟩ := hs
    exact ⟨lo,fun t _ => hl t⟩
  · exact hn

def LeastColumnPeriod (xs : List Bool) (P : Nat) : Prop :=
  0<P ∧ Periodic (tr xs) P ∧ ∀ k, 0<k → Periodic (tr xs) k → P≤k

/-- Least COLUMN period, not the period of the complete prefix. -/
theorem least_column_above_four_transfer (xs : List Bool) (P : Nat)
    (hP : 4<P) (hp : LeastColumnPeriod xs P) (hs : SpanOne (tr xs)) :
    ∃ ys : List Bool, ys.length+1=xs.length ∧ CedarSafety.Safe ys ∧ evolution 8 ys≠ys := by
  apply alltime_height_one_shorter_counterexample xs hs
  intro h4
  have h := hp.2.2 4 (by decide) h4
  omega

end HeightOnePeriodicity
