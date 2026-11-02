module
public import GateScopeAudit
public import NonperiodicHiddenExample
@[expose] public section
namespace RightRecurrent
open Ruliology.CellularAutomata.Rule30Jen PeriodTwoGateExclusion

/-- Two closed19-step paths in the SIX-cell two-step relaxation. The outer
input is free. Neither a full right extension nor finite origin is asserted. -/
def rows (q : Bool) : List Nat := if q then
  [63,32,27,28,9,35,22,31,0,3,14,63,0,3,14,63,0,3,14] else
  [63,0,3,14,63,32,27,28,9,35,22,31,0,3,14,63,0,3,14]
def controls (q : Bool) : List Nat := if q then
  [2,0,1,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0] else
  [0,0,0,0,2,0,1,1,0,0,0,1,0,0,0,0,0,0,0]
def decode (w : Nat) : Window :=
  (w.testBit 0,w.testBit 1,w.testBit 2,w.testBit 3,w.testBit 4,w.testBit 5)
def win (q : Bool) (p : Nat) : Window := decode ((rows q)[p]?.getD 0)
def ctl (q : Bool) (p k : Nat) : Bool := ((controls q)[p]?.getD 0).testBit k
def raw (q : Bool) (p : Nat) : Bool := output (win q p)
def orbit (q : Nat → Bool) (n : Nat) : Window := win (q (n/19)) (n%19)
def input (q : Nat → Bool) (n k : Nat) : Bool := ctl (q (n/19)) (n%19) k
def f (q : Nat → Bool) (n : Nat) : Bool := output (orbit q n)

theorem transition_certificate : ∀ q next : Bool, ∀ p : Fin 19,
    (p.val<18 → next=q) → win next ((p.val+1)%19)=
      step2 (win q p.val) (ctl q p.val 0) (ctl q p.val 1) := by decide

theorem orbit_step (q : Nat → Bool) (n : Nat) : orbit q (n+1)=
    step2 (orbit q n) (input q n 0) (input q n 1) := by
  have hc : n%19<18 → q ((n+1)/19)=q (n/19) := by
    intro h; congr 1; omega
  have h:=transition_certificate (q (n/19)) (q ((n+1)/19))
    ⟨n%19,Nat.mod_lt _ (by decide)⟩ hc
  simpa [orbit,input,Nat.add_mod] using h

/-- Explicit intermediate rows: every single step in the finite strip obeys
Rule30, with alternating center driver and free outer boundary. -/
def strip (q : Nat → Bool) (t : Nat) : Window :=
  if t%2=0 then orbit q (t/2) else step true (orbit q (t/2)) (input q (t/2) 0)
def boundary (q : Nat → Bool) (t : Nat) : Bool := input q (t/2) (t%2)
theorem strip_step (q : Nat → Bool) (t : Nat) :
    strip q (t+1)=step (decide (t%2=0)) (strip q t) (boundary q t) := by
  by_cases h : t%2=0
  · have h1 : (t+1)%2=1 := by omega
    have h2 : (t+1)/2=t/2 := by omega
    simp [strip,boundary,h,h1,h2]
  · have h1 : t%2=1 := by omega
    have h2 : (t+1)%2=0 := by omega
    have h3 : (t+1)/2=t/2+1 := by omega
    simp only [strip,h1,h2,h3,ite_true,boundary]
    exact orbit_step q (t/2)

theorem local_gate (a b : Bool) : rule (a||b) false (rule true a b)=true := by
  cases a <;> cases b <;> rfl
/-- The f trace is the actual left-neighbor value required by the center equation
in this finite strip, not an arbitrary auxiliary output attached to the graph. -/
theorem center_step (q : Nat → Bool) (t : Nat) :
    decide ((t+1)%2=0)=rule (if t%2=0 then true else f q (t/2))
      (decide (t%2=0)) (strip q t).1 := by
  by_cases h : t%2=0
  · have h1 : (t+1)%2=1 := by omega
    simp [h,h1,rule]
  · have h1 : (t+1)%2=0 := by omega
    simp only [h,h1,ite_false,decide_false,decide_true,strip]
    exact (local_gate (orbit q (t/2)).1 (orbit q (t/2)).2.1).symm

def short (q next : Bool) (p k : Nat) : Bool :=
  raw (if p+k<19 then q else next) ((p+k)%19)
theorem f_add (q : Nat → Bool) (n k : Nat) (hk : k<19) :
    f q (n+k)=short (q (n/19)) (q (n/19+1)) (n%19) k := by
  unfold f orbit short
  by_cases h : n%19+k<19
  · have hq : (n+k)/19=n/19 := by omega
    simp only [ite_eq_left h,hq,raw]
    congr 2; omega
  · have hq : (n+k)/19=n/19+1 := by omega
    simp only [ite_eq_right h,hq,raw]
    congr 2; omega

theorem elementary_certificate : ∀ q next : Bool, ∀ p : Fin 19,
    (short q next p.val 0=false → short q next p.val 1=true) ∧
    ¬(∀ k : Fin 5,short q next p.val k.val=true) := by decide
theorem no00 (q : Nat → Bool) (n : Nat) : f q n=false → f q (n+1)=true := by
  have h:=(elementary_certificate (q (n/19)) (q (n/19+1))
    ⟨n%19,Nat.mod_lt _ (by decide)⟩).1
  have h0:=f_add q n 0 (by decide)
  have h1:=f_add q n 1 (by decide)
  simpa only [Nat.add_zero] using h0.symm ▸ (h1.symm ▸ h)
theorem no11111 (q : Nat → Bool) (n : Nat) : ¬(∀ k : Fin 5,f q (n+k.val)=true) := by
  intro h
  apply (elementary_certificate (q (n/19)) (q (n/19+1))
    ⟨n%19,Nat.mod_lt _ (by decide)⟩).2
  intro k
  rw [←f_add q n k.val (by omega)]
  exact h k

theorem block_sample (q : Nat → Bool) (n k : Nat) (hk : k<19) :
    f q (19*n+k)=raw (q n) k := by
  have h1 : (19*n+k)/19=n := by omega
  have h2 : (19*n+k)%19=k := by omega
  simp [f,orbit,h1,h2,raw]
theorem reads_schedule (q : Nat → Bool) (n : Nat) : f q (19*n+5)=q n := by
  rw [block_sample q n 5 (by decide)]
  cases q n <;> rfl
theorem periodic_iff_schedule (q : Nat → Bool) :
    EventuallyPeriodic (f q) ↔ EventuallyPeriodic q := by
  constructor
  · rintro ⟨T,P,hP,hper⟩
    refine ⟨T,P,hP,?_⟩
    intro n hn
    have h:=periodic_mul hper 19 (19*n+5) (by omega)
    rw [show 19*n+5+19*P=19*(n+P)+5 by omega,reads_schedule,reads_schedule] at h
    exact h
  · rintro ⟨T,P,hP,hper⟩
    refine ⟨19*T,19*P,by omega,?_⟩
    intro n hn
    have hd : (n+19*P)/19=n/19+P := by omega
    have hm : (n+19*P)%19=n%19 := by omega
    simp only [f,orbit,hd,hm,hper (n/19) (by omega)]
theorem not_periodic (q : Nat → Bool) (hq : ¬EventuallyPeriodic q) :
    ¬EventuallyPeriodic (f q) := by
  rintro ⟨T,P,hP,hper⟩
  apply hq
  refine ⟨T,P,hP,?_⟩
  intro n hn
  have h:=periodic_mul hper 19 (19*n+5) (by omega)
  rw [show 19*n+5+19*P=19*(n+P)+5 by omega,reads_schedule,reads_schedule] at h
  exact h

set_option maxRecDepth 4096 in
theorem bad_certificate : ∀ q : Bool, ∀ w : Fin 256,w.val∈GateScopeAudit.S →
    ∃ k : Fin 8,w.val.testBit k.val≠ !(raw q k.val) := by decide
theorem bad_every_block (q : Nat → Bool) (n : Nat) :
    ¬GateScopeAudit.SWindow (fun t => !(f q t)) (19*n) := by
  rintro ⟨w,hw,hbits⟩
  obtain ⟨k,hk⟩:=bad_certificate (q n) w hw
  have hb:=hbits k
  change w.val.testBit k.val= !(f q (19*n+k.val)) at hb
  rw [block_sample q n k.val (by omega)] at hb
  exact hk hb
theorem not_eventually_S (q : Nat → Bool) :
    ¬(∃ T,∀ t,T≤t → GateScopeAudit.SWindow (fun n => !(f q n)) t) := by
  rintro ⟨T,hT⟩
  exact bad_every_block q T (hT (19*T) (by omega))

/-- A concrete all-time counterexample to eventual-S-or-periodic IN THE FINITE
STRIP MODEL. Arbitrary concatenation need not be aperiodic; the chosen schedule is.
No assertion is made about satisfying the equation outside the six-cell strip. -/
theorem counterexample : ∃ q : Nat → Bool,
    (∀ n,orbit q (n+1)=step2 (orbit q n) (input q n 0) (input q n 1)) ∧
    (∀ n,f q n=false → f q (n+1)=true) ∧
    (∀ n,¬(∀ k : Fin 5,f q (n+k.val)=true)) ∧
    ¬EventuallyPeriodic (f q) ∧
    ¬(∃ T,∀ t,T≤t → GateScopeAudit.SWindow (fun n => !(f q n)) t) := by
  refine ⟨NonperiodicHiddenExample.powers,orbit_step _,no00 _,no11111 _,?_,not_eventually_S _⟩
  exact not_periodic _ NonperiodicHiddenExample.powers_not_periodic

#print axioms strip_step
#print axioms center_step
#print axioms periodic_iff_schedule
#print axioms not_periodic
#print axioms counterexample
end RightRecurrent
