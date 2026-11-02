module
public import Ruliology.CellularAutomata.Rule30DrivenMaskTransport
@[expose] public section
namespace PeriodicHiddenPair
open Ruliology.CellularAutomata Rule30DrivenLeft Rule30DrivenMaskTransport

/-! A period-eleven, bounded hidden pair with an infinite common left background.
This is NOT a finite-origin counterexample. The finite truncations depend on H. -/
def words (b : Bool) : List Nat :=
  if b then [4,15,56,36,62,33,51,46,41,15,56]
  else [0,1,35,54,37,61,33,51,46,9,63]
def driver (t : Nat) : Bool := decide (t%11<2)
def window (b : Bool) (t k : Nat) : Bool :=
  ((words b)[t%11]?.getD 0).testBit k
def outer (t : Nat) : Bool := window false t 5
def upstream (t : Nat) : Bool := ([0,1,0,0,0,0,0,0,1,1,1] : List Nat)[t%11]?.getD 0 == 1
def past : Nat → Nat → Bool
  | 0,t => outer t
  | 1,t => upstream t
  | n+2,t => xor (past (n+1) (t+1)) (past (n+1) t || past n t)
def profile (b : Bool) (t k : Nat) : Bool :=
  if k=0 then effective driver t
  else if k<6 then window b t (k-1) else past (k-6) t
def start (b : Bool) (p : Int) : Bool := profile b 0 p.natAbs

theorem local_certificate : ∀ b : Bool, ∀ t : Fin 11, ∀ k : Fin 6,
    profile b (t.val+1) (k.val+1) = Rule30Jen.rule
      (profile b t.val (k.val+2)) (profile b t.val (k.val+1)) (profile b t.val k.val) := by decide

theorem physical_step (b : Bool) (t k : Nat) :
    profile b (t+1) (k+1) = Rule30Jen.rule
      (profile b t (k+2)) (profile b t (k+1)) (profile b t k) := by
  by_cases hk : k<6
  · have h := local_certificate b ⟨t%11,Nat.mod_lt _ (by decide)⟩
    have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | simpa [profile,past,outer,upstream,window,driver,effective,Nat.add_mod] using h ⟨0,by decide⟩
      | simpa [profile,past,outer,upstream,window,driver,effective,Nat.add_mod] using h ⟨1,by decide⟩
      | simpa [profile,past,outer,upstream,window,driver,effective,Nat.add_mod] using h ⟨2,by decide⟩
      | simpa [profile,past,outer,upstream,window,driver,effective,Nat.add_mod] using h ⟨3,by decide⟩
      | simpa [profile,past,outer,upstream,window,driver,effective,Nat.add_mod] using h ⟨4,by decide⟩
      | simpa [profile,past,outer,upstream,window,driver,effective,Nat.add_mod] using h ⟨5,by decide⟩
  · obtain ⟨n,rfl⟩ : ∃ n,k=n+6 := ⟨k-6,by omega⟩
    simp only [profile,show ¬n+6+1=0 by omega,show ¬n+6+2=0 by omega,
      show ¬n+6=0 by omega,show ¬n+6+1<6 by omega,show ¬n+6+2<6 by omega,
      show ¬n+6<6 by omega,Nat.add_sub_cancel,
      show n+6+1-6=n+1 by omega,show n+6+2-6=n+2 by omega,past,Rule30Jen.rule]
    cases past (n+1) (t+1) <;> cases past (n+1) t <;> cases past n t <;> rfl

theorem actual_evolution (b : Bool) : ∀ t k : Nat,
    L (effective driver) (start b) t (-(k : Int)) = profile b t k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => exact L_col0 0
    | succ k => rw [L_zero (by omega)]; rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => exact L_col0 (t+1)
    | succ k =>
      rw [L_succ (by omega),
        show -((k+1 : Nat) : Int)-1 = -((k+2 : Nat) : Int) by omega,
        show -((k+1 : Nat) : Int)+1 = -(k : Int) by omega,
        ih (k+2),ih (k+1),ih k]
      exact (physical_step b t k).symm

theorem pin_certificate : ∀ b : Bool, ∀ t : Fin 11,
    driver t.val=true → profile b t.val 1= !driver (t.val+1) := by decide
theorem pinned_forever (b : Bool) : EffectiveConsistent driver (start b) := by
  intro t ht
  rw [show (-1 : Int)= -((1 : Nat) : Int) by rfl,actual_evolution]
  have h := pin_certificate b ⟨t%11,Nat.mod_lt _ (by decide)⟩
  simpa [profile,window,driver,Nat.add_mod] using h (by simpa [driver] using ht)

theorem distinct_certificate : ∀ t : Fin 11, ∃ k : Fin 6,
    0<k.val ∧ profile false t.val k.val ≠ profile true t.val k.val := by decide
theorem distinct_forever (t : Nat) : ∃ k : Nat, 0<k ∧ k<6 ∧
    L (effective driver) (start false) t (-(k : Int)) ≠
    L (effective driver) (start true) t (-(k : Int)) := by
  obtain ⟨k,hk,hd⟩ := distinct_certificate ⟨t%11,Nat.mod_lt _ (by decide)⟩
  refine ⟨k.val,hk,k.isLt,?_⟩
  rw [actual_evolution,actual_evolution]
  simpa [profile,window,show ¬k.val=0 by omega,k.isLt] using hd

theorem common_background (t k : Nat) (hk : 6≤k) :
    L (effective driver) (start false) t (-(k : Int)) =
    L (effective driver) (start true) t (-(k : Int)) := by
  rw [actual_evolution,actual_evolution]
  simp [profile,show ¬k=0 by omega,show ¬k<6 by omega]

theorem driver_periodic (t : Nat) : driver (t+11)=driver t := by simp [driver]
theorem driver_both : BothValues driver := ⟨⟨2,rfl⟩,⟨0,rfl⟩⟩

theorem start_not_finite (b : Bool) : ¬FiniteNonzeroLeft (start b) := by
  rintro ⟨m,hm,hwhite,hblack⟩
  apply no_periodic_column (c:=effective driver) (s:=start b) hwhite hblack hm
    (q:= -1) (hq:=by decide)
  · refine ⟨0,11,by decide,?_⟩
    intro t ht
    simp [effective,driver,Nat.add_mod]
  · refine ⟨0,11,by decide,?_⟩
    intro t ht
    change L (effective driver) (start b) (t+11) (-((1 : Nat) : Int)) =
      L (effective driver) (start b) t (-((1 : Nat) : Int))
    rw [actual_evolution,actual_evolution]
    simp [profile,window]

#print axioms physical_step
#print axioms actual_evolution
#print axioms pinned_forever
#print axioms distinct_forever
#print axioms common_background
#print axioms start_not_finite
end PeriodicHiddenPair
