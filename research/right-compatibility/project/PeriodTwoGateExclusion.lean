module
public import HiddenPairRightObstruction
@[expose] public section
namespace PeriodTwoGateExclusion
open Ruliology.CellularAutomata.Rule30Jen HiddenPairRightObstruction

abbrev Window := Bool × Bool × Bool × Bool × Bool × Bool
def step (c : Bool) (w : Window) (b : Bool) : Window :=
  let (a0,a1,a2,a3,a4,a5):=w
  (rule c a0 a1,rule a0 a1 a2,rule a1 a2 a3,rule a2 a3 a4,rule a3 a4 a5,rule a4 a5 b)
def step2 (w : Window) (b0 b1 : Bool) : Window := step false (step true w b0) b1
def output (w : Window) : Bool := w.1 || w.2.1
def encode (w : Window) : Nat :=
  let (a0,a1,a2,a3,a4,a5):=w
  a0.toNat+2*a1.toNat+4*a2.toNat+8*a3.toNat+16*a4.toNat+32*a5.toNat
def subsets : List Nat := [18446744073709551615,156080254134420010,5893339205845141704,
  153265461283291648,92605301719040072,14411598249586606144,0]
abbrev member (n : Nat) (w : Window) : Prop := (subsets[n]?.getD 0).testBit (encode w)=true
def word (n : Nat) : Bool := ([false,true,false,true,true,false][n]?.getD false)

theorem initial_certificate : ∀ a b c d e f : Bool,member 0 (a,b,c,d,e,f) := by decide
theorem transition_certificate : ∀ n : Fin 6, ∀ a b c d e f u v : Bool,
    member n.val (a,b,c,d,e,f) → output (a,b,c,d,e,f)=word n.val →
    member (n.val+1) (step2 (a,b,c,d,e,f) u v) := by decide

theorem initial (w : Window) : member 0 w := by
  rcases w with ⟨a,b,c,d,e,f⟩
  exact initial_certificate a b c d e f
theorem transition (n : Nat) (hn : n<6) (w : Window) (u v : Bool)
    (hm : member n w) (ho : output w=word n) : member (n+1) (step2 w u v) := by
  rcases w with ⟨a,b,c,d,e,f⟩
  exact transition_certificate ⟨n,hn⟩ a b c d e f u v hm ho
theorem final_empty (w : Window) : ¬member 6 w := by simp [member,subsets]

def window (X : Nat → Int → Bool) (t : Nat) : Window :=
  (X t 1,X t 2,X t 3,X t 4,X t 5,X t 6)
theorem window_step {X : Nat → Int → Bool} (hX : FullHistory X) (t : Nat) :
    window X (t+1)=step (X t 0) (window X t) (X t 7) := by
  unfold window step
  rw [hX t 1,hX t 2,hX t 3,hX t 4,hX t 5,hX t 6]
  rfl

theorem gate_identity (a b ell : Bool) (h : true=rule ell false (rule true a b)) :
    ell=(a||b) := by
  cases a <;> cases b <;> cases ell <;> first | rfl | cases h

theorem actual_output {X : Nat → Int → Bool} (hX : FullHistory X) (t : Nat)
    (h0 : X t 0=true) (h1 : X (t+1) 0=false) (h2 : X (t+2) 0=true) :
    X (t+1) (-1)=output (window X t) := by
  have er:=hX t 1
  change X (t+1) 1=rule (X t 0) (X t 1) (X t 2) at er
  rw [h0] at er
  have ec:=hX (t+1) 0
  change X (t+2) 0=rule (X (t+1) (-1)) (X (t+1) 0) (X (t+1) 1) at ec
  rw [h1,h2,er] at ec
  exact gate_identity _ _ _ ec

/-- Any full Rule30 history with thirteen alternating center cells cannot have
the left free-bit block010110 at its six intervening white times. No finite-origin
assumption is needed. The six-cell finite check proves one invariant step only. -/
theorem no_010110 {X : Nat → Int → Bool} (hX : FullHistory X) (T : Nat)
    (hc : ∀ i,i≤12 → X (T+i) 0=decide (i%2=0)) :
    ¬(∀ n,n<6 → X (T+2*n+1) (-1)=word n) := by
  intro hg
  have invariant : ∀ n,n≤6 → member n (window X (T+2*n)) := by
    intro n
    induction n with
    | zero => intro hn;simpa using initial (window X T)
    | succ n ih =>
      intro hn
      have h0 : X (T+2*n) 0=true := by rw [hc (2*n) (by omega)];simp
      have h1 : X (T+2*n+1) 0=false := by
        rw [show T+2*n+1=T+(2*n+1) by omega,hc (2*n+1) (by omega)]
        simp [Nat.add_mod]
      have h2 : X (T+2*n+2) 0=true := by
        rw [show T+2*n+2=T+(2*n+2) by omega,hc (2*n+2) (by omega)]
        simp
      have ho : output (window X (T+2*n))=word n :=
        (actual_output hX (T+2*n) h0 h1 h2).symm.trans (hg n (by omega))
      have ht:=transition n (by omega) (window X (T+2*n))
        (X (T+2*n) 7) (X (T+2*n+1) 7) (ih (by omega)) ho
      rw [show T+2*(n+1)=(T+2*n+1)+1 by omega,window_step hX,h1,
        window_step hX,h0]
      exact ht
  exact final_empty _ (invariant 6 (by decide))

#print axioms transition_certificate
#print axioms no_010110
end PeriodTwoGateExclusion
