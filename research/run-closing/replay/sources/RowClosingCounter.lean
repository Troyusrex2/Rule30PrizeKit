module
public import RunClosing
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# An exact unrestricted-boundary counterexample to universal top-slice closing

The gate 01 has period two; its odd-black boundary has period four. Its
official reconstructed left half is spatially periodic after the wall,
with seven temporal profiles. Two inverse states remain distinct forever
on its next row. This gate is NOT S-legal. No finite-support counterexample,
no counterexample to S-legal closing, and no prize solution is claimed.
-/
@[expose] public section
namespace RowClosingCounter
open RunClosing Ruliology.CellularAutomata.Rule30ZeroBoundary

def profiles : List Nat := [11,6,12,8,8,12,10]
def profile (t k : Nat) : Bool := (profiles[k%7]?.getD 0).testBit (t%4)
def boundary (t : Nat) : Bool := (11:Nat).testBit (t%4)
def full (k t : Nat) : Bool := if k=0 then false else profile t (k+6)
def initial (k : Nat) : Bool := full k 0
def gate (r : Nat) : Bool := decide (r%2=1)

theorem profile_mod (t k : Nat) : profile (t%4) (k%7)=profile t k := by
  simp only [profile,Nat.mod_mod]

theorem profile_add_seven (t k : Nat) : profile t (k+7)=profile t k := by
  simp [profile]

theorem full_root (t : Nat) : full 1 t=boundary t := by
  simp [full,profile,boundary,profiles]

theorem bulk_certificate : ∀ k : Fin 7, ∀ t : Fin 4,
    profile t.val (k.val+2)=xor (profile (t.val+1) (k.val+1))
      (profile t.val (k.val+1)||profile t.val k.val) := by decide

theorem head_certificate : ∀ t : Fin 4,
    full 2 t.val=xor (full 1 (t.val+1)) (full 1 t.val||full 0 t.val) := by decide

theorem full_step (k t : Nat) :
    full (k+2) t=xor (full (k+1) (t+1)) (full (k+1) t||full k t) := by
  by_cases hk : k=0
  · subst k
    have h := head_certificate ⟨t%4,Nat.mod_lt _ (by decide)⟩
    simpa [full,profile,boundary,Nat.add_mod] using h
  · have hk1 : ¬k+1=0 := by omega
    have hk2 : ¬k+2=0 := by omega
    simp only [full,hk,hk1,hk2,ite_false]
    have h := bulk_certificate ⟨(k+6)%7,Nat.mod_lt _ (by decide)⟩
      ⟨t%4,Nat.mod_lt _ (by decide)⟩
    have i1 : ((k+6)%7+1)%7=(k+1+6)%7 := by omega
    have i2 : ((k+6)%7+2)%7=(k+2+6)%7 := by omega
    have j : (t%4+1)%4=(t+1)%4 := by omega
    simpa only [profile,Nat.mod_mod,i1,i2,j] using h

theorem full_recon : ∀ k t, full k t=recon boundary k t
  | 0,t => rfl
  | 1,t => full_root t
  | k+2,t => by
    rw [full_step,full_recon (k+1) (t+1),full_recon (k+1) t,full_recon k t]
    rfl

theorem initial_evolution (t k : Nat) : zrow initial t k=full k t := by
  have he : initial=lam boundary := by
    funext k
    exact full_recon k 0
  rw [he,zrow_lam]
  exact (full_recon k t).symm

theorem boundary_gate_certificate : ∀ t : Fin 4,
    (11:Nat).testBit t.val=
      (if t.val%2=0 then !(decide ((t.val/2)%2=1)) else true) := by decide

theorem boundary_gate (t : Nat) : boundary t=oddBlack gate t := by
  have hp : t%2=(t%4)%2 := by omega
  have hd : (t/2)%2=(t%4)/2 := by omega
  have hr : ((t%4)/2)%2=(t%4)/2 := by omega
  have h := boundary_gate_certificate ⟨t%4,Nat.mod_lt _ (by decide)⟩
  simpa only [boundary,oddBlack,gate,hp,hd,hr] using h

theorem root_odd_black (r : Nat) : zrow initial (2*r+1) 1=true := by
  rw [initial_evolution,full_root,boundary_gate]
  have ho : (2*r+1)%2≠0 := by omega
  simp only [oddBlack,ho,ite_false]

theorem gate_not_S :
    (List.range 8).foldl (fun w i => w+(gate i).toNat*2^i) 0 ∉
      ([8,9,16,18,33,36,66,72,132,144] : List Nat) := by decide

def futureWord : List Bool := [true,true,false,false,false,false,true]

theorem future_certificate : ∀ k : Fin 7,
    profile 1 k.val=futureWord[k.val]! := by decide

theorem forward_initial (k : Nat) : forward initial k=futureWord[k%7]! := by
  have hk : k+1≠0 := by omega
  have hc := future_certificate ⟨k%7,Nat.mod_lt _ (by decide)⟩
  unfold forward initial
  rw [full_step k 0]
  have cancel (a b : Bool) : xor (xor a b) b=a := by cases a <;> cases b <;> rfl
  rw [cancel]
  simp only [full,hk,ite_false,show k+1+6=k+7 by omega,profile_add_seven]
  simpa only [profile,Nat.mod_mod] using hc

def pathA : List State := [(true,false),(false,true),(false,false),(false,false),
  (false,false),(false,false),(false,false)]
def pathB : List State := [(false,true),(false,false),(true,false),(true,true),
  (true,true),(true,true),(true,true)]
def stateAt (p : List State) (k : Nat) : State := p[k%7]?.getD (false,false)

theorem paths_certificate : ∀ k : Fin 7,
    stateAt pathA k.val≠stateAt pathB k.val ∧
    transfer futureWord[k.val]! (stateAt pathA k.val)=stateAt pathA (k.val+1) ∧
    transfer futureWord[k.val]! (stateAt pathB k.val)=stateAt pathB (k.val+1) := by decide

theorem paths_step (p : List State) (hp : p=pathA ∨ p=pathB) (k : Nat) :
    transfer (forward initial k) (stateAt p k)=stateAt p (k+1) := by
  rw [forward_initial]
  have h := paths_certificate ⟨k%7,Nat.mod_lt _ (by decide)⟩
  rcases hp with rfl|rfl
  · simpa [stateAt,Nat.add_mod] using h.2.1
  · simpa [stateAt,Nat.add_mod] using h.2.2

theorem paths_scan (p : List State) (hp : p=pathA ∨ p=pathB) (k n : Nat) :
    scan (segment (forward initial) k n) (stateAt p k)=stateAt p (k+n) := by
  induction n generalizing k with
  | zero => simp [segment,scan]
  | succ n ih =>
    simp only [segment,scan,paths_step p hp]
    have h := ih (k+1)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem no_prefix_synchronizes (n : Nat) :
    ¬Synchronized (segment (forward initial) 0 n) := by
  intro h
  have he := h (stateAt pathA 0).1 (stateAt pathA 0).2 (stateAt pathB 0).1 (stateAt pathB 0).2
  rw [paths_scan pathA (Or.inl rfl),paths_scan pathB (Or.inr rfl)] at he
  have hd := (paths_certificate ⟨n%7,Nat.mod_lt _ (by decide)⟩).1
  exact hd (by simpa only [Nat.zero_add,stateAt,Nat.mod_mod] using he)

theorem no_segment_synchronizes (d n : Nat) :
    ¬Synchronized (segment (forward initial) d n) := by
  intro h
  have he := h (stateAt pathA d).1 (stateAt pathA d).2 (stateAt pathB d).1 (stateAt pathB d).2
  rw [paths_scan pathA (Or.inl rfl),paths_scan pathB (Or.inr rfl)] at he
  have hd := (paths_certificate ⟨(d+n)%7,Nat.mod_lt _ (by decide)⟩).1
  exact hd (by simpa only [stateAt,Nat.mod_mod] using he)

/-- An all-depth failure for this unrestricted forced row. -/
theorem unrestricted_closing_false : ¬RowClosing initial := by
  intro h
  have ht := (tail_closing_iff (forward initial)).mp ((row_closing_iff initial).mp h)
  obtain ⟨n,hn⟩ := ht 0
  exact no_prefix_synchronizes n hn

def rowOne (k : Nat) : Bool := full k 1

theorem forward_row_one (k : Nat) : forward rowOne k=full (k+1) 2 := by
  unfold forward rowOne
  rw [full_step k 1]
  have cancel (a b : Bool) : xor (xor a b) b=a := by cases a <;> cases b <;> rfl
  exact cancel _ _

theorem phase_one_reset (d : Nat) :
    segment (forward rowOne) (7*d+4) 4=[false,true,false,false] := by
  simp [segment,forward_row_one,full,profile,profiles,Nat.add_mod]
  decide

/-- A change of time phase genuinely changes the closing property. -/
theorem phase_one_closes : RowClosing rowOne := by
  rw [row_closing_iff]
  intro d
  refine ⟨7*d+4,4,by omega,?_⟩
  rw [phase_one_reset]
  exact run_resets 0 false

theorem actual_phase_dependence :
    ¬RowClosing initial ∧ RowClosing (fun k => zrow initial 1 k) := by
  refine ⟨unrestricted_closing_false,?_⟩
  have h : (fun k => zrow initial 1 k)=rowOne := by
    funext k
    exact initial_evolution 1 k
  rw [h]
  exact phase_one_closes

end RowClosingCounter
