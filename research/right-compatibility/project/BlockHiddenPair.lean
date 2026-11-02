module
public import PeriodicHiddenPair
@[expose] public section
namespace BlockHiddenPair
open Ruliology.CellularAutomata Rule30DrivenLeft Rule30DrivenMaskTransport
open PeriodicHiddenPair (driver)

def words (choice branch : Bool) : List Nat :=
  if choice then
    if branch then [28,19,30,17,27,18,63,0,32,48,8,28,19,30,17,27,18,63,0,32,48,8]
    else [24,21,21,21,21,21,53,5,45,41,15,24,21,21,21,21,21,53,5,45,41,15]
  else
    if branch then [28,51,46,41,47,40,44,10,27,50,15,24,53,37,61,33,51,46,9,31,48,8]
    else [24,53,37,61,33,51,46,9,31,48,8,28,51,46,41,47,40,44,10,27,50,15]
def input (choice : Bool) : List Bool :=
  if choice then [true,true,true,true,true,false,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,false]
  else [false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,true,false,false,true,false]
def cells (choice branch : Bool) (phase k : Nat) : Bool :=
  if k=0 then effective driver phase
  else if k=7 then (input choice)[phase]?.getD false
  else ((words choice branch)[phase]?.getD 0).testBit (k-1)
def head (q : Nat → Bool) (b : Bool) (t k : Nat) : Bool := cells (q (t/22)) b (t%22) k

theorem head_certificate : ∀ choice next branch : Bool, ∀ p : Fin 22, ∀ k : Fin 6,
    (p.val<21 → next=choice) →
    cells next branch ((p.val+1)%22) (k.val+1) = Rule30Jen.rule
      (cells choice branch p.val (k.val+2)) (cells choice branch p.val (k.val+1))
      (cells choice branch p.val k.val) := by decide
theorem common_certificate : ∀ choice branch : Bool, ∀ p : Fin 22,
    cells choice branch p.val 6=cells choice false p.val 6 ∧
    cells choice branch p.val 7=cells choice false p.val 7 := by decide

theorem head_step (q : Nat → Bool) (b : Bool) (t k : Nat) (hk : k<6) :
    head q b (t+1) (k+1)=Rule30Jen.rule (head q b t (k+2)) (head q b t (k+1)) (head q b t k) := by
  have hc : t%22<21 → q ((t+1)/22)=q (t/22) := by
    intro h
    congr 1
    omega
  have h:=head_certificate (q (t/22)) (q ((t+1)/22)) b ⟨t%22,Nat.mod_lt _ (by decide)⟩ ⟨k,hk⟩ hc
  simpa [head,Nat.add_mod] using h

def past (q : Nat → Bool) : Nat → Nat → Bool
  | 0,t => head q false t 6
  | 1,t => head q false t 7
  | n+2,t => xor (past q (n+1) (t+1)) (past q (n+1) t || past q n t)
def profile (q : Nat → Bool) (b : Bool) (t k : Nat) : Bool :=
  if k<6 then head q b t k else past q (k-6) t
def start (q : Nat → Bool) (b : Bool) (p : Int) : Bool := profile q b 0 p.natAbs

theorem profile_head (q : Nat → Bool) (b : Bool) (t k : Nat) (hk : k≤7) :
    profile q b t k=head q b t k := by
  by_cases h : k<6
  · simp only [profile,ite_eq_left h]
  · have cert := common_certificate (q (t/22)) b ⟨t%22,Nat.mod_lt _ (by decide)⟩
    have cases : k=6 ∨ k=7 := by omega
    rcases cases with rfl|rfl
    · exact cert.1.symm
    · exact cert.2.symm

theorem profile_zero (q : Nat → Bool) (b : Bool) (t : Nat) : profile q b t 0=effective driver t := by
  have h0 : (t%22)%11=t%11 := by omega
  have h1 : (t%22+1)%11=(t+1)%11 := by omega
  simp [profile,head,cells,effective,driver,h0,h1]

theorem physical_step (q : Nat → Bool) (b : Bool) (t k : Nat) :
    profile q b (t+1) (k+1)=Rule30Jen.rule
      (profile q b t (k+2)) (profile q b t (k+1)) (profile q b t k) := by
  by_cases hk : k<6
  · rw [profile_head q b (t+1) (k+1) (by omega),profile_head q b t (k+2) (by omega),
      profile_head q b t (k+1) (by omega),profile_head q b t k (by omega)]
    exact head_step q b t k hk
  · obtain ⟨n,rfl⟩ : ∃ n,k=n+6 := ⟨k-6,by omega⟩
    simp only [profile,show ¬n+6+1<6 by omega,show ¬n+6+2<6 by omega,
      show ¬n+6<6 by omega,Nat.add_sub_cancel,
      show n+6+1-6=n+1 by omega,show n+6+2-6=n+2 by omega,past,Rule30Jen.rule]
    cases past q (n+1) (t+1) <;> cases past q (n+1) t <;> cases past q n t <;> rfl

theorem actual_evolution (q : Nat → Bool) (b : Bool) : ∀ t k : Nat,
    L (effective driver) (start q b) t (-(k : Int))=profile q b t k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => rw [profile_zero]; exact L_col0 0
    | succ k => rw [L_zero (by omega)]; rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => rw [profile_zero]; exact L_col0 (t+1)
    | succ k =>
      rw [L_succ (by omega),
        show -((k+1 : Nat) : Int)-1 = -((k+2 : Nat) : Int) by omega,
        show -((k+1 : Nat) : Int)+1 = -(k : Int) by omega,
        ih (k+2),ih (k+1),ih k]
      exact (physical_step q b t k).symm

theorem pin_certificate : ∀ choice branch : Bool, ∀ p : Fin 22,
    driver p.val=true → cells choice branch p.val 1= !driver (p.val+1) := by decide
theorem pinned_forever (q : Nat → Bool) (b : Bool) : EffectiveConsistent driver (start q b) := by
  intro t ht
  rw [show (-1 : Int)= -((1 : Nat) : Int) by rfl,actual_evolution,profile_head q b t 1 (by decide)]
  have h0 : (t%22)%11=t%11 := by omega
  have h1 : (t%22+1)%11=(t+1)%11 := by omega
  have h := pin_certificate (q (t/22)) b ⟨t%22,Nat.mod_lt _ (by decide)⟩
  simpa [head,driver,h0,h1] using h (by simpa [driver,h0] using ht)

theorem distinct_certificate : ∀ choice : Bool, ∀ p : Fin 22, ∃ k : Fin 6,
    0<k.val ∧ cells choice false p.val k.val ≠ cells choice true p.val k.val := by decide
theorem distinct_forever (q : Nat → Bool) (t : Nat) : ∃ k : Nat,0<k ∧ k<6 ∧
    L (effective driver) (start q false) t (-(k : Int)) ≠
    L (effective driver) (start q true) t (-(k : Int)) := by
  obtain ⟨k,hk,hd⟩ := distinct_certificate (q (t/22)) ⟨t%22,Nat.mod_lt _ (by decide)⟩
  refine ⟨k.val,hk,k.isLt,?_⟩
  rw [actual_evolution,actual_evolution,profile_head q false t k.val (by omega),
    profile_head q true t k.val (by omega)]
  exact hd

theorem common_background (q : Nat → Bool) (t k : Nat) (hk : 6≤k) :
    L (effective driver) (start q false) t (-(k : Int))=
    L (effective driver) (start q true) t (-(k : Int)) := by
  rw [actual_evolution,actual_evolution]
  simp [profile,show ¬k<6 by omega]

theorem reads_schedule (q : Nat → Bool) (b : Bool) (n : Nat) :
    L (effective driver) (start q b) (22*n) (-7)=q n := by
  change L (effective driver) (start q b) (22*n) (-((7 : Nat) : Int))=q n
  rw [actual_evolution,profile_head q b (22*n) 7 (by decide)]
  simp only [head,Nat.mul_mod_right,Nat.mul_div_right _ (by decide : 0<22)]
  cases q n <;> rfl

theorem periodic_sample22 {f : Nat → Bool} (hf : Rule30Jen.EventuallyPeriodic f) (offset : Nat) :
    Rule30Jen.EventuallyPeriodic (fun n => f (22*n+offset)) := by
  obtain ⟨T,P,hP,h⟩:=hf
  refine ⟨T,P,hP,?_⟩
  intro t ht
  have key := Rule30Jen.periodic_mul h 22 (22*t+offset) (by omega)
  simpa only [show 22*t+offset+22*P=22*(t+P)+offset by omega] using key

theorem upstream_not_periodic (q : Nat → Bool) (hq : ¬Rule30Jen.EventuallyPeriodic q) (b : Bool) :
    ¬Rule30Jen.EventuallyPeriodic (fun t => L (effective driver) (start q b) t (-7)) := by
  intro h
  have hh:=periodic_sample22 h 0
  have hs : (fun n => L (effective driver) (start q b) (22*n+0) (-7))=q := by
    funext n
    exact reads_schedule q b n
  rw [hs] at hh
  exact hq hh

/-- A hidden bounded defect does not force any periodic common column to its left.
Finite origin is still absent: arbitrary schedules generate infinite-left starts. -/
theorem deeper_not_periodic (q : Nat → Bool) (hq : ¬Rule30Jen.EventuallyPeriodic q) (b : Bool) :
    ∀ n : Nat, ¬Rule30Jen.EventuallyPeriodic
      (fun t => L (effective driver) (start q b) t (-((n+7 : Nat) : Int))) := by
  intro n
  induction n with
  | zero => exact upstream_not_periodic q hq b
  | succ n ih =>
    intro h
    have h0 : Rule30Jen.EventuallyPeriodic (fun t => L (effective driver) (start q b) t 0) := by
      refine ⟨0,11,by decide,?_⟩
      intro t ht
      simp [L_col0,effective,driver,Nat.add_mod]
    have hn := between_periodic (j:= -((n+1+7 : Nat) : Int)) (k:=0) (by omega) (by omega) h h0
    rw [show -((n+1+7 : Nat) : Int)+1= -((n+7 : Nat) : Int) by omega] at hn
    exact ih hn

#print axioms actual_evolution
#print axioms pinned_forever
#print axioms distinct_forever
#print axioms common_background
#print axioms reads_schedule
#print axioms upstream_not_periodic
#print axioms deeper_not_periodic
end BlockHiddenPair
