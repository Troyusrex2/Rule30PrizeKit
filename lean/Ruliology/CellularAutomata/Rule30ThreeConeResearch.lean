module

public import Ruliology.CellularAutomata.Rule30ThreePrefixResearch
public import Ruliology.CellularAutomata.Rule30PackedReconstructionResearch

/-!
# Sound inverse-cone certificates for the constrained period-three left half

Generalize the catalog's zero-boundary sideways reconstruction to any driver.
Every constrained initial prefix of length N is represented by ceil(N/3)
free temporal bits. `coneCheck_sound` connects ordinary-kernel finite checks
to the actual driven-left evolution, for every choice of the size parameters.

This is a certificate method, not an unbounded-width termination proof.
The basic reconstruction and packed update extend the existing catalog
methods; no priority or prize solution is claimed.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ThreeConeResearch

open Rule30DrivenLeft Rule30EtherThree Rule30ThreePrefixResearch
open Rule30PackedReconstructionResearch

def recon (c a : Nat → Bool) : Nat → Nat → Bool
  | 0,t => c t
  | 1,t => a t
  | k+2,t => xor (recon c a (k+1) (t+1))
      (recon c a (k+1) t || recon c a k t)

theorem recon_two (c a : Nat → Bool) (k t : Nat) :
    recon c a (k+2) t=xor (recon c a (k+1) (t+1))
      (recon c a (k+1) t || recon c a k t) := rfl

theorem history_eq_recon (c : Nat → Bool) (s : Int → Bool) :
    ∀ k t : Nat, L c s t (-(k:Int))=recon c (fun t => L c s t (-1)) k t := by
  have key : ∀ k : Nat,
      (∀ t, L c s t (-(k:Int))=recon c (fun t => L c s t (-1)) k t) ∧
      (∀ t, L c s t (-((k+1:Nat):Int))=recon c (fun t => L c s t (-1)) (k+1) t) := by
    intro k
    induction k with
    | zero =>
        constructor
        · intro t; simpa [recon] using (L_col0 (c:=c) (s:=s) t)
        · intro t; rfl
    | succ k ih =>
        refine ⟨ih.2,fun t => ?_⟩
        have hx := L_left (c:=c) (s:=s) t (p:= -((k+1:Nat):Int)) (by omega)
        rw [show -((k+1:Nat):Int)-1= -((k+2:Nat):Int) by omega,
          show -((k+1:Nat):Int)+1= -(k:Int) by omega] at hx
        rw [recon_two,← ih.2 (t+1),← ih.2 t,← ih.1 t]
        exact hx
  exact fun k t => (key k).1 t

theorem packed_sound (A B H : Nat) (c a : Nat → Bool)
    (hc : ∀ t, t<H → A.testBit t=c t)
    (ha : ∀ t, t<H → B.testBit t=a t) : ∀ k t, t+k<H →
    (advance k A B).1.testBit t=recon c a k t ∧
      (advance k A B).2.testBit t=recon c a (k+1) t := by
  intro k
  induction k with
  | zero =>
      intro t ht
      exact ⟨by simpa [advance_zero,recon] using hc t (by omega),
        by simpa [advance_zero,recon] using ha t (by omega)⟩
  | succ k ih =>
      intro t ht
      have h0 := ih t (by omega)
      have h1 := ih (t+1) (by omega)
      rw [advance_last]
      refine ⟨h0.2,?_⟩
      simp only [Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftRight]
      rw [show 1+t=t+1 by omega,h1.2,h0.2,h0.1]
      exact (recon_two c a k t).symm

def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => pack f n ^^^ ((f n).toNat <<< n)

theorem pack_bit (f : Nat → Bool) : ∀ n j,
    (pack f n).testBit j=if j<n then f j else false := by
  intro n
  induction n with
  | zero => intro j; simp [pack]
  | succ n ih =>
      intro j
      by_cases hj : j<n
      · simp [pack,Nat.testBit_xor,Nat.testBit_shiftLeft,Nat.testBit_bool_toNat,
          ih,hj,show ¬n≤j by omega,show j<n+1 by omega]
      · by_cases he : j=n
        · subst j
          cases hf : f n <;> simp [pack,Nat.testBit_xor,Nat.testBit_shiftLeft,ih,hf]
        · simp [pack,Nat.testBit_xor,Nat.testBit_shiftLeft,Nat.testBit_bool_toNat,
            ih,hj,show n≤j by omega,show ¬j<n+1 by omega,show j-n≠0 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n<2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  simp [pack_bit,show ¬j<n by omega]

def modeHead (m t : Nat) : Bool :=
  if t%3=0 then m.testBit (t/3) else decide (t%3=2)

def driverCode (N : Nat) : Nat := pack driver N
def modeCode (N m : Nat) : Nat := pack (modeHead m) N

noncomputable def code (N m k : Nat) : Bool :=
  (advance k (driverCode N) (modeCode N m)).2.testBit 0

def FitsPrefix (s : Int → Bool) (N : Nat) : Prop :=
  ∀ t, t<N → fits3 (colPattern3 w011) (t%3) (L driver s t (-1))=true

theorem prefix_head_code {s : Int → Bool} (N : Nat) (hs : FitsPrefix s N) :
    ∃ m, m<2^((N+2)/3) ∧ ∀ t, t<N → modeHead m t=L driver s t (-1) := by
  let m := pack (fun n => L driver s (3*n) (-1)) ((N+2)/3)
  refine ⟨m,pack_lt _ _,fun t ht => ?_⟩
  by_cases hphase : t%3=0
  · have hdiv : t/3<(N+2)/3 := by omega
    have heq : 3*(t/3)=t := by omega
    simp [modeHead,hphase,m,pack_bit,hdiv,heq]
  · have hc := hs t ht
    rw [fits3_011] at hc
    have hp : t%3=1 ∨ t%3=2 := by omega
    rcases hp with hp | hp <;>
      cases hv : L driver s t (-1) <;> simp [hp,hv] at hc ⊢ <;>
      simp [modeHead,hp]

theorem constrained_head_code {s : Int → Bool} (hs : Constrained s) (N : Nat) :
    ∃ m, m<2^((N+2)/3) ∧ ∀ t, t<N → modeHead m t=L driver s t (-1) :=
  prefix_head_code N (fun t _ => hs t)

/-- Finite trace agreement suffices for exact code coverage, for every size. -/
theorem prefix_code {s : Int → Bool} (N : Nat) (hs : FitsPrefix s N) :
    ∃ m, m<2^((N+2)/3) ∧ ∀ k, k<N →
      s (-((k+1:Nat):Int))=code N m k := by
  obtain ⟨m,hm,hhead⟩ := prefix_head_code N hs
  refine ⟨m,hm,fun k hk => ?_⟩
  have h := packed_sound (driverCode N) (modeCode N m) N driver
    (fun t => L driver s t (-1))
    (fun t ht => by simp [driverCode,pack_bit,ht])
    (fun t ht => by simpa [modeCode,pack_bit,ht] using hhead t ht) k 0 (by omega)
  have hx := history_eq_recon driver s (k+1) 0
  rw [L_zero (by omega)] at hx
  exact hx.trans h.2.symm

theorem constrained_code {s : Int → Bool} (hs : Constrained s) (N : Nat) :
    ∃ m, m<2^((N+2)/3) ∧ ∀ k, k<N →
      s (-((k+1:Nat):Int))=code N m k :=
  prefix_code N (fun t _ => hs t)

noncomputable def coneCheck (W N : Nat) : Bool :=
  (List.range (2^((N+2)/3))).all fun m =>
    (List.range (N-W)).any fun j => code N m (W+j)

/-- A true certificate excludes all starts white beyond W, for every W and N. -/
theorem coneCheck_prefix_sound (W N : Nat) (hcheck : coneCheck W N=true)
    (s : Int → Bool) (hwhite : ∀ p : Int, p< -(W:Int) → s p=false) :
    ¬FitsPrefix s N := by
  intro hs
  obtain ⟨m,hm,hcode⟩ := prefix_code N hs
  have hall := List.all_eq_true.mp hcheck m (List.mem_range.mpr hm)
  obtain ⟨j,hj,hblack⟩ := List.any_eq_true.mp hall
  have hj' : j<N-W := List.mem_range.mp hj
  have he := hcode (W+j) (by omega)
  have hw := hwhite (-((W+j+1:Nat):Int)) (by omega)
  rw [hw,hblack] at he
  cases he

theorem coneCheck_sound (W N : Nat) (hcheck : coneCheck W N=true)
    (s : Int → Bool) (hwhite : ∀ p : Int, p< -(W:Int) → s p=false) :
    ¬Constrained s :=
  fun hs => coneCheck_prefix_sound W N hcheck s hwhite (fun t _ => hs t)

/-- A true finite certificate supplies an actual forced-phase violation before N. -/
theorem coneCheck_failure (W N : Nat) (hcheck : coneCheck W N=true)
    (s : Int → Bool) (hwhite : ∀ p : Int, p< -(W:Int) → s p=false) :
    ∃ t, t<N ∧ fits3 (colPattern3 w011) (t%3) (L driver s t (-1))=false := by
  apply Classical.byContradiction
  intro hno
  apply coneCheck_prefix_sound W N hcheck s hwhite
  intro t ht
  cases hb : fits3 (colPattern3 w011) (t%3) (L driver s t (-1))
  · exact False.elim (hno ⟨t,ht,hb⟩)
  · rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- Small regression certificate for the general method, not a new numerical bound. -/
theorem cone8_checked : coneCheck 8 17=true := by decide +kernel

theorem width8_excluded (s : Int → Bool)
    (hwhite : ∀ p : Int, p< -8 → s p=false) : ¬Constrained s :=
  coneCheck_sound 8 17 cone8_checked s hwhite

theorem width8_failure (s : Int → Bool)
    (hwhite : ∀ p : Int, p< -8 → s p=false) :
    ∃ t, t<17 ∧ fits3 (colPattern3 w011) (t%3) (L driver s t (-1))=false :=
  coneCheck_failure 8 17 cone8_checked s hwhite

end Ruliology.CellularAutomata.Rule30ThreeConeResearch
