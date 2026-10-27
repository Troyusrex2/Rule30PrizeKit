module
public import Rule30CAClockDemodulationResearch

/-! Exact responses to changing appended initial bits, and a necessary and
sufficient all-time criterion for positive-order filters to erase them.
The prefix is any nonempty actual finite CA tail. No period is supplied. -/
@[expose] public section
namespace Rule30CAResponseFilterResearch
open Rule30CAObserverResearch Rule30CAClockDemodulationResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def diff (v : Nat → Bool) (t : Nat) := xor (v (t+1)) (v t)
def filtered : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, v => v
  | n+1, v => filtered n (diff v)
def responseR (u : List Bool) (g h g' h' : Bool) (t : Nat) :=
  xor (outR (u++[g,h]) t) (outR (u++[g',h']) t)
def responseS (u : List Bool) (g h g' h' : Bool) (t : Nat) :=
  xor (outS (u++[g,h]) t) (outS (u++[g',h']) t)
def chi (u : List Bool) (t : Nat) := xor (outR u t) (outS u t)

theorem xor_shuffle (a b c d : Bool) :
    xor (xor a b) (xor c d)=xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem xor_zero (a b : Bool) : xor a b=false ↔ a=b := by
  cases a <;> cases b <;> decide +kernel
theorem masked_sum (q a b : Bool) :
    xor (q && !a) (q && !b)=(q && xor a b) := by
  cases q <;> cases a <;> cases b <;> rfl
theorem cancel_middle (a b c : Bool) :
    xor (xor a b) (xor c b)=xor a c := by
  cases a <;> cases b <;> cases c <;> rfl
theorem xor_recover (a b c : Bool) (h : xor a b=c) : b=xor a c := by
  cases a <;> cases b <;> cases c <;> cases h <;> rfl

theorem g_initial_response (u : List Bool) (g g' : Bool) (t : Nat) :
    xor (giter u g t) (giter u g' t)=xor g g' := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [giter,xor_same_right] using ih

/-- Different initial penultimate bits expose the older observations through
two cross-run XORs. Both trajectories retain the same actual older prefix. -/
theorem response_constraints (u : List Bool) (hu : u≠[])
    (g h g' h' : Bool) (t : Nat) :
    xor (responseR u g h g' h' t) (responseS u g h g' h' t)=
      (xor g g' && !(outR u t)) ∧
    xor (responseS u g h g' h' t) (responseR u g h g' h' (t+1))=
      (xor g g' && !(outS u t)) := by
  constructor
  · dsimp only [responseR,responseS]
    rw [xor_shuffle,(observation_ors u g h hu t).1,
      (observation_ors u g' h' hu t).1,or_difference,g_initial_response]
  · dsimp only [responseR,responseS]
    rw [xor_shuffle,(observation_ors u g h hu t).2,
      (observation_ors u g' h' hu t).2]
    rw [or_difference]
    simp only [halfBit,xor_same_right,g_initial_response]

theorem response_derivative (u : List Bool) (hu : u≠[])
    (g h g' h' : Bool) :
    diff (responseR u g h g' h')=(fun t => xor g g' && chi u t) := by
  funext t
  have hh := response_constraints u hu g h g' h' t
  have hc : xor (xor (responseS u g h g' h' t) (responseR u g h g' h' (t+1)))
      (xor (responseR u g h g' h' t) (responseS u g h g' h' t))=
      xor (responseR u g h g' h' (t+1)) (responseR u g h g' h' t) := by
    cases responseS u g h g' h' t <;> cases responseR u g h g' h' (t+1) <;>
      cases responseR u g h g' h' t <;> rfl
  rw [hh.1,hh.2,masked_sum] at hc
  dsimp only [diff,chi]
  rw [← hc]
  cases outR u t <;> cases outS u t <;> rfl

theorem filtered_xor (n : Nat) (a b : Nat → Bool) :
    filtered n (fun t => xor (a t) (b t))=
      (fun t => xor (filtered n a t) (filtered n b t)) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
      have hh : diff (fun t => xor (a t) (b t))=
          (fun t => xor (diff a t) (diff b t)) := by
        funext t
        exact xor_shuffle _ _ _ _
      simp only [filtered,hh,ih]

theorem filtered_mask (n : Nat) (q : Bool) (a : Nat → Bool) :
    filtered n (fun t => q && a t)=(fun t => q && filtered n a t) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      have hh : diff (fun t => q && a t)=(fun t => q && diff a t) := by
        funext t
        cases q <;> rfl
      simp only [filtered,hh,ih]

theorem filtered_not (n : Nat) (a : Nat → Bool) :
    filtered (n+1) (fun t => !(a t))=filtered (n+1) a := by
  have hh : diff (fun t => !(a t))=diff a := by
    funext t
    dsimp only [diff]
    cases a (t+1) <;> cases a t <;> rfl
  simp only [filtered,hh]

/-- Complete filtered response formula, uniform in filter order, prefix
length, phase, and both appended initial pairs. -/
theorem filtered_response (u : List Bool) (hu : u≠[])
    (g h g' h' : Bool) (n t : Nat) :
    filtered (n+1) (responseR u g h g' h') t=
      (xor g g' && filtered n (chi u) t) ∧
    filtered (n+1) (responseS u g h g' h') t=
      (xor g g' && xor (filtered n (chi u) t) (filtered (n+1) (outR u) t)) := by
  have hr : filtered (n+1) (responseR u g h g' h')=
      (fun t => xor g g' && filtered n (chi u) t) := by
    rw [filtered,response_derivative u hu,filtered_mask]
  have hs : responseS u g h g' h'=(fun t => xor (responseR u g h g' h' t)
      (xor g g' && !(outR u t))) := by
    funext t
    exact xor_recover _ _ _ (response_constraints u hu g h g' h' t).1
  refine ⟨congrFun hr t,?_⟩
  rw [hs,filtered_xor,filtered_mask,filtered_not,hr]
  cases xor g g' <;> rfl

def ErasesPair (u : List Bool) (n : Nat) : Prop :=
  ∀ g h g' h' t,
    filtered n (outR (u++[g,h])) t=filtered n (outR (u++[g',h'])) t ∧
    filtered n (outS (u++[g,h])) t=filtered n (outS (u++[g',h'])) t

theorem responseR_eq (u : List Bool) (g h g' h' : Bool) :
    responseR u g h g' h'=(fun t => xor (outR (u++[g,h]) t) (outR (u++[g',h']) t)) := rfl
theorem responseS_eq (u : List Bool) (g h g' h' : Bool) :
    responseS u g h g' h'=(fun t => xor (outS (u++[g,h]) t) (outS (u++[g',h']) t)) := rfl

/-- A positive-order filter erases both appended initial bits exactly when
the two stated older-stream differences vanish at every time. No return or
period premise is assumed, and no spatial inheritance is concluded. -/
theorem erases_pair_iff (u : List Bool) (hu : u≠[]) (n : Nat) :
    ErasesPair u (n+1) ↔
      ∀ t, filtered n (chi u) t=false ∧ filtered (n+1) (outR u) t=false := by
  constructor
  · intro he t
    have hp := he false false true false t
    have hf := filtered_response u hu false false true false n t
    have hr : filtered (n+1) (responseR u false false true false) t=false := by
      rw [responseR_eq,filtered_xor]
      exact (xor_zero _ _).mpr hp.1
    have hs : filtered (n+1) (responseS u false false true false) t=false := by
      rw [responseS_eq,filtered_xor]
      exact (xor_zero _ _).mpr hp.2
    have hc : filtered n (chi u) t=false := by simpa only [Bool.false_xor,Bool.true_and] using hf.1.symm.trans hr
    refine ⟨hc,?_⟩
    have hh := hf.2.symm.trans hs
    simpa only [Bool.false_xor,Bool.true_and,hc] using hh
  · intro he g h g' h' t
    have hf := filtered_response u hu g h g' h' n t
    have hh := he t
    constructor
    · apply (xor_zero _ _).mp
      have hx := hf.1
      rw [hh.1,Bool.and_false] at hx
      simpa only [responseR_eq,filtered_xor] using hx
    · apply (xor_zero _ _).mp
      have hx := hf.2
      rw [hh.1,hh.2] at hx
      simpa only [responseS_eq,filtered_xor,Bool.false_xor,Bool.and_false] using hx

end Rule30CAResponseFilterResearch
