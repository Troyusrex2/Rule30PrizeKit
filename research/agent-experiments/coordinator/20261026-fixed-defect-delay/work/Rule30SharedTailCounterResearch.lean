module
public import Ruliology.CellularAutomata.Rule30Prize

/-! A finite-difference, infinite-tail obstruction to boundary-free
separation. The two histories share the entire right tail and a nonconstant
adjacent column. A permanent source difference is invisible at the head.
These starts are NOT right bounded and give no counterexample to the reader
or to Problem 1. The older eight-clock period-loss orbit is a precursor. -/
@[expose] public section
namespace Rule30SharedTailCounterResearch
open Ruliology.CellularAutomata
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

abbrev State := Nat → Bool
def step (x : State) (k : Nat) : Bool :=
  Rule30Jen.rule (x k) (x (k+1)) (x (k+2))
def orbit (x : State) : Nat → State
  | 0 => x
  | t+1 => step (orbit x t)
def Finite (x : State) : Prop := ∃ N, ∀ k, N≤k → x k=false

def key (k : Nat) : Nat := if k<5 then k else 5+(k-5)%4
def nextKey (i : Nat) : Nat := if i<8 then i+1 else 5
theorem key_lt (k : Nat) : key k<9 := by unfold key;split <;> omega
theorem key_succ (k : Nat) : key (k+1)=nextKey (key k) := by
  unfold key nextKey
  split <;> split <;> split <;> omega

def profile (which : Bool) (i : Nat) : Nat :=
  (if which then [170,93,162,83,178,202,43,172,178]
   else [170,170,117,138,77,202,43,172,178]).getD i 0
def frame (which : Bool) (t k : Nat) : Bool := (profile which (key k)).testBit (t%8)
def initial (which : Bool) : State := frame which 0

theorem step_table : ∀ which : Bool, ∀ t i : Fin 9, t.val<8 →
    (profile which i.val).testBit ((t.val+1)%8)=
      Rule30Jen.rule ((profile which i.val).testBit t.val)
        ((profile which (nextKey i.val)).testBit t.val)
        ((profile which (nextKey (nextKey i.val))).testBit t.val) := by decide +kernel

theorem frame_step (which : Bool) (t : Nat) : step (frame which t)=frame which (t+1) := by
  funext k
  have h := step_table which ⟨t%8,by omega⟩ ⟨key k,key_lt k⟩ (Nat.mod_lt _ (by decide))
  simpa only [step,frame,key_succ,show k+2=(k+1)+1 by omega,
    show (t+1)%8=(t%8+1)%8 by omega] using h.symm

theorem orbit_frame (which : Bool) : ∀ t, orbit (initial which) t=frame which t
  | 0 => rfl
  | t+1 => by rw [orbit,orbit_frame,frame_step]

theorem full_period_eight (which : Bool) (t : Nat) :
    orbit (initial which) (t+8)=orbit (initial which) t := by
  rw [orbit_frame,orbit_frame]
  funext k
  simp [frame]

theorem shared_tail (t k : Nat) (hk : 5≤k) :
    orbit (initial true) t k=orbit (initial false) t k := by
  have h : ∀ i : Fin 9, 5≤i.val → profile true i.val=profile false i.val := by decide +kernel
  have hkey : 5≤key k := by unfold key;rw [ite_eq_right (by omega)];omega
  rw [orbit_frame,orbit_frame]
  dsimp [frame]
  rw [h ⟨key k,key_lt k⟩ hkey]

theorem heads_equal (t : Nat) : orbit (initial true) t 0=orbit (initial false) t 0 := by
  rw [orbit_frame,orbit_frame]
  rfl

theorem source_opposite (t : Nat) :
    orbit (initial true) t 4≠orbit (initial false) t 4 := by
  have h : ∀ t : Fin 8, (profile true 4).testBit t.val≠(profile false 4).testBit t.val := by decide +kernel
  simpa only [orbit_frame,frame,key,show 4<5 by decide,ite_true] using
    h ⟨t%8,Nat.mod_lt _ (by decide)⟩

theorem common_neighbor_nonconstant :
    orbit (initial true) 0 5≠orbit (initial true) 1 5 := by
  rw [orbit_frame,orbit_frame]
  decide +kernel

theorem initial_difference_finite :
    Finite (fun k => xor (initial true k) (initial false k)) := by
  refine ⟨5,?_⟩
  intro k hk
  have h := shared_tail 0 k hk
  change initial true k=initial false k at h
  change xor (initial true k) (initial false k)=false
  rw [h]
  cases initial false k <;> rfl

theorem initial_infinite (which : Bool) : ¬Finite (initial which) := by
  rintro ⟨W,hW⟩
  have h := hW (4*(W+1)+6) (by omega)
  have hk : key (4*(W+1)+6)=6 := by unfold key;rw [ite_eq_right (by omega)];omega
  change (profile which (key (4*(W+1)+6))).testBit 0=false at h
  rw [hk] at h
  cases which <;> contradiction

/-- Explicit failure of separation with finite difference but an infinite shared tail. -/
theorem shared_tail_resynchronization : ∃ x y : State,
    Finite (fun k => xor (x k) (y k)) ∧ ¬Finite x ∧ ¬Finite y ∧
    (∀ t k, 5≤k → orbit x t k=orbit y t k) ∧
    (∀ t, orbit x t 4≠orbit y t 4) ∧
    orbit x 0 5≠orbit x 1 5 ∧ (∀ t, orbit x t 0=orbit y t 0) := by
  exact ⟨initial true,initial false,initial_difference_finite,initial_infinite true,
    initial_infinite false,shared_tail,source_opposite,common_neighbor_nonconstant,heads_equal⟩

end Rule30SharedTailCounterResearch
