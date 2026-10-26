module
public import Rule30SharedTailCounterResearch
public import Rule30SharedTailDelayResearch

/-! One initial bit can be invisible at a nonalternating observed ray when
the shared right tail is infinite. This refutes proposed finite-difference
weakenings of the finite-background hypothesis; it does not refute the
right-bounded reader or Problem 1. -/
@[expose] public section
namespace Rule30SingleFlipTailResearch
open Ruliology.CellularAutomata
open Rule30SharedTailCounterResearch (State step orbit Finite)
open Rule30SharedTailDelayResearch (cut cut_finite orbit_cut source_stays_opposite tail_stays_shared)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def key (k : Nat) : Nat := if k<8 then k else 8+(k-8)%4
def nextKey (i : Nat) : Nat := if i<11 then i+1 else 8
theorem key_lt (k : Nat) : key k<12 := by unfold key;split <;> omega
theorem key_succ (k : Nat) : key (k+1)=nextKey (key k) := by
  unfold key nextKey
  split <;> split <;> split <;> omega

def profile (which : Bool) (i : Nat) : Nat :=
  (if which then [168,212,172,178,202,43,172,178,202,43,172,178]
   else [168,180,204,170,170,117,138,77,202,43,172,178]).getD i 0
def frame (which : Bool) (t k : Nat) : Bool := (profile which (key k)).testBit (t%8)
def initial (which : Bool) : State := frame which 0

theorem step_table : ∀ which : Bool, ∀ t : Fin 8, ∀ i : Fin 12,
    (profile which i.val).testBit ((t.val+1)%8)=
      Rule30Jen.rule ((profile which i.val).testBit t.val)
        ((profile which (nextKey i.val)).testBit t.val)
        ((profile which (nextKey (nextKey i.val))).testBit t.val) := by decide +kernel

theorem frame_step (which : Bool) (t : Nat) : step (frame which t)=frame which (t+1) := by
  funext k
  have h := step_table which ⟨t%8,Nat.mod_lt _ (by decide)⟩ ⟨key k,key_lt k⟩
  simpa only [step,frame,key_succ,show k+2=(k+1)+1 by omega,
    show (t+1)%8=(t%8+1)%8 by omega] using h.symm

theorem orbit_frame (which : Bool) : ∀ t, orbit (initial which) t=frame which t
  | 0 => rfl
  | t+1 => by rw [orbit,orbit_frame,frame_step]

theorem period_eight (which : Bool) (t : Nat) :
    orbit (initial which) (t+8)=orbit (initial which) t := by
  rw [orbit_frame,orbit_frame]
  funext k
  simp [frame]

theorem shared_tail (t k : Nat) (hk : 8≤k) :
    orbit (initial true) t k=orbit (initial false) t k := by
  have h : ∀ i : Fin 12, 8≤i.val → profile true i.val=profile false i.val := by decide +kernel
  have hkey : 8≤key k := by unfold key;rw [ite_eq_right (by omega)];omega
  rw [orbit_frame,orbit_frame]
  dsimp [frame]
  rw [h ⟨key k,key_lt k⟩ hkey]

theorem single_initial_flip (k : Nat) : initial true k≠initial false k ↔ k=7 := by
  by_cases hk : 8≤k
  · have he := shared_tail 0 k hk
    change initial true k=initial false k at he
    simp [he,show k≠7 by omega]
  · have h : ∀ k : Fin 8, initial true k.val≠initial false k.val ↔ k.val=7 := by decide +kernel
    exact h ⟨k,by omega⟩

theorem initial_true_formula (k : Nat) : initial true k=decide (5≤k ∧ k%4=1) := by
  by_cases hk : k<8
  · have h : ∀ k : Fin 8, initial true k.val=decide (5≤k.val ∧ k.val%4=1) := by decide +kernel
    exact h ⟨k,hk⟩
  · have hkey : key k=8+k%4 := by unfold key;rw [ite_eq_right hk];omega
    have h : ∀ j : Fin 4, (profile true (8+j.val)).testBit 0=decide (j.val=1) := by decide +kernel
    simpa [initial,frame,hkey,show 5≤k by omega] using h ⟨k%4,Nat.mod_lt _ (by decide)⟩

theorem initial_false_formula (k : Nat) :
    initial false k=decide ((5≤k ∧ k%4=1) ∨ k=7) := by
  by_cases hk : k=7
  · subst k;decide +kernel
  · have he : initial false k=initial true k := by
      by_cases he : initial true k=initial false k
      · exact he.symm
      · exact False.elim (hk ((single_initial_flip k).mp he))
    rw [he,initial_true_formula]
    simp [hk]

theorem source_opposite (t : Nat) :
    orbit (initial true) t 7≠orbit (initial false) t 7 := by
  have h : ∀ t : Fin 8, (profile true 7).testBit t.val≠(profile false 7).testBit t.val := by decide +kernel
  simpa only [orbit_frame,frame,key,show 7<8 by decide,ite_true] using
    h ⟨t%8,Nat.mod_lt _ (by decide)⟩

theorem heads_equal (t : Nat) : orbit (initial true) t 0=orbit (initial false) t 0 := by
  rw [orbit_frame,orbit_frame]
  rfl

theorem head_not_period_two : ¬∀ t, orbit (initial true) (t+2) 0=orbit (initial true) t 0 := by
  intro h
  have hh := h 1
  rw [orbit_frame,orbit_frame] at hh
  contradiction

theorem common_OR (t : Nat) :
    (orbit (initial true) t 1 || orbit (initial true) t 2)=
      (orbit (initial false) t 1 || orbit (initial false) t 2) := by
  have h : ∀ t : Fin 8,
      ((profile true 1).testBit t.val || (profile true 2).testBit t.val)=
      ((profile false 1).testBit t.val || (profile false 2).testBit t.val) := by decide +kernel
  simpa only [orbit_frame,frame,key,show 1<8 by decide,show 2<8 by decide,ite_true] using
    h ⟨t%8,Nat.mod_lt _ (by decide)⟩

theorem OR_nonconstant :
    (orbit (initial true) 0 1 || orbit (initial true) 0 2)=false ∧
    (orbit (initial true) 2 1 || orbit (initial true) 2 2)=true := by
  simp only [orbit_frame]
  decide +kernel

theorem neighbors_differ : orbit (initial true) 5 1≠orbit (initial false) 5 1 := by
  rw [orbit_frame,orbit_frame]
  decide +kernel

theorem initial_infinite (which : Bool) : ¬Finite (initial which) := by
  rintro ⟨W,hW⟩
  have h := hW (4*(W+1)+9) (by omega)
  have hk : key (4*(W+1)+9)=9 := by unfold key;rw [ite_eq_right (by omega)];omega
  change (profile which (key (4*(W+1)+9))).testBit 0=false at h
  rw [hk] at h
  cases which <;> contradiction

/-- A shared right tail and even a single initial flip do not ensure visibility. -/
theorem single_flip_invisible : ∃ x y : State,
    (∀ k, x k≠y k ↔ k=7) ∧ ¬Finite x ∧ ¬Finite y ∧
    (∀ t k, 8≤k → orbit x t k=orbit y t k) ∧
    (∀ t, orbit x t 7≠orbit y t 7) ∧
    (∀ t, orbit x t 0=orbit y t 0) ∧
    ¬(∀ t, orbit x (t+2) 0=orbit x t 0) := by
  exact ⟨initial true,initial false,single_initial_flip,initial_infinite true,
    initial_infinite false,shared_tail,source_opposite,heads_equal,head_not_period_two⟩

/-- Even a one-cell defect has no background-independent visibility deadline. -/
theorem arbitrary_finite_single_flip_delay (T : Nat) : ∃ x y : State,
    Finite x ∧ Finite y ∧
    (∀ k, 2*T+16≤k → x k=false ∧ y k=false) ∧
    (∀ k, x k≠y k ↔ k=7) ∧
    (∀ t k, 8≤k → orbit x t k=orbit y t k) ∧
    (∀ t, orbit x t 7≠orbit y t 7) ∧
    (∀ t, t≤T → orbit x t 0=orbit y t 0) := by
  let N := 2*T+16
  let x := cut (initial true) N
  let y := cut (initial false) N
  have hflip : ∀ k, x k≠y k ↔ k=7 := by
    intro k
    change cut (initial true) N k≠cut (initial false) N k ↔ k=7
    by_cases hk : k<N
    · simp only [cut,hk,ite_true]
      exact single_initial_flip k
    · simp [cut,hk,show k≠7 by dsimp [N] at hk;omega]
  have ht : ∀ k, 8≤k → x k=y k := by
    intro k hk
    by_cases he : x k=y k
    · exact he
    · have h7 := (hflip k).mp he
      omega
  have hbound : ∀ k, N≤k → x k=false ∧ y k=false := by
    intro k hk
    constructor <;> exact ite_eq_right (by omega)
  refine ⟨x,y,cut_finite _ N,cut_finite _ N,hbound,hflip,
    tail_stays_shared x y 8 ht,source_stays_opposite x y 7 ht ((hflip 7).mpr rfl),?_⟩
  intro t htT
  rw [show orbit x t 0=orbit (initial true) t 0 from orbit_cut _ N t 0 (by dsimp [N];omega),
      show orbit y t 0=orbit (initial false) t 0 from orbit_cut _ N t 0 (by dsimp [N];omega)]
  exact heads_equal t

end Rule30SingleFlipTailResearch
