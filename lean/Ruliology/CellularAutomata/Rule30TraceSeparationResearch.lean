module

public import Ruliology.CellularAutomata.Rule30TraceEdgeResearch

/-!
# Kernel-checkable separation of traces with fixed finite left edges

There is NO hypothesis on the right half, including no finiteness hypothesis.
For H observations, only the initial cells through H-1 on the right matter.
We enumerate each side's possible traces separately and check disjointness.
This is a bounded certificate method, not a proof of EdgeObservable.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30TraceSeparationResearch

open Rule30Jen Rule30Realization Rule30TraceEdgeResearch

/-- Moving-frame integer Rule 30, using only core Lean. -/
def Phi (a : Nat) : Nat := a ^^^ ((a <<< 1) ||| (a <<< 2))

def orbit (a : Nat) : Nat → Nat
  | 0 => a
  | t+1 => Phi (orbit a t)

def row (a : Nat) (p : Int) : Bool := if p≤0 then a.testBit (-p).toNat else false

theorem evol_row_white (a : Nat) : ∀ (t : Nat) (p : Int), (t:Int)<p → evol (row a) t p = false
  | 0,p,hp => by simp [evol,row,show ¬ p≤0 by omega]
  | t+1,p,hp => by
    change rule (evol (row a) t (p-1)) (evol (row a) t p) (evol (row a) t (p+1)) = false
    rw [evol_row_white a t (p-1) (by omega),evol_row_white a t p (by omega),
        evol_row_white a t (p+1) (by omega)]
    rfl

theorem testBit_orbit (a : Nat) : ∀ t j,
    (orbit a t).testBit j = evol (row a) t ((t:Int)-j)
  | 0,j => by
    simp only [orbit,evol,row]
    rw [ite_eq_left (by omega)]
    congr 1
    omega
  | t+1,j => by
    have hc : (decide (1≤j) && (orbit a t).testBit (j-1)) =
        evol (row a) t (((t+1:Nat):Int)-j) := by
      cases j with
      | zero =>
        rw [evol_row_white a t _ (by omega)]
        rfl
      | succ j =>
        rw [show decide (1≤j+1)=true by simp,Bool.true_and,
            show j+1-1=j by omega,testBit_orbit a t j]
        congr 1
        omega
    have hr : (decide (2≤j) && (orbit a t).testBit (j-2)) =
        evol (row a) t (((t+1:Nat):Int)-j+1) := by
      rcases j with _ | _ | j
      · rw [evol_row_white a t _ (by omega)]; rfl
      · rw [evol_row_white a t _ (by omega)]; rfl
      · rw [show decide (2≤j+2)=true by simp,Bool.true_and,
            show j+2-2=j by omega,testBit_orbit a t j]
        congr 1
        omega
    rw [orbit,Phi,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,
        testBit_orbit a t j,hc,hr]
    change rule (evol (row a) t ((t:Int)-j))
        (evol (row a) t (((t+1:Nat):Int)-j)) (evol (row a) t (((t+1:Nat):Int)-j+1)) =
      rule (evol (row a) t ((((t+1:Nat):Int)-j)-1))
        (evol (row a) t (((t+1:Nat):Int)-j)) (evol (row a) t (((t+1:Nat):Int)-j+1))
    congr 2
    omega

def pack (x : Int → Bool) (C : Nat) : Nat → Nat
  | 0 => 0
  | K+1 => pack x C K ||| ((x ((C:Int)-K)).toNat <<< K)

theorem testBit_bool (b : Bool) (k : Nat) : b.toNat.testBit k = (decide (k=0) && b) := by
  exact Nat.testBit_bool_toNat b k

theorem testBit_pack (x : Int → Bool) (C : Nat) : ∀ K k,
    (pack x C K).testBit k = (decide (k<K) && x ((C:Int)-k))
  | 0,k => by simp [pack]
  | K+1,k => by
    rw [pack,Nat.testBit_or,testBit_pack x C K k,Nat.testBit_shiftLeft,testBit_bool]
    by_cases hk : k<K
    · simp [hk,show k<K+1 by omega,show ¬ K≤k by omega]
    · by_cases he : k=K
      · subst he; simp
      · simp [hk,show ¬ k<K+1 by omega,show k-K≠0 by omega]

theorem pack_lt (x : Int → Bool) (C K : Nat) : pack x C K < 2^K := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_pack]
  simp [show ¬ i<K by omega]

def centeredRow (C a : Nat) (p : Int) : Bool := row a (p-C)

theorem centered_row_agrees {x : Int → Bool} {m C : Nat}
    (hx : HasLeftEdge x (-(m:Int))) :
    ∀ p : Int, p≤(C:Int) → centeredRow C (2^(C+m)+pack x C (C+m)) p = x p := by
  intro p hp
  unfold centeredRow row
  rw [ite_eq_left (by omega)]
  have hk : (-(p-(C:Int))).toNat = ((C:Int)-p).toNat := by congr 1; omega
  rw [hk]
  have hbits := Nat.testBit_two_pow_mul_add 1 (pack_lt x C (C+m)) (((C:Int)-p).toNat)
  simp only [Nat.mul_one] at hbits
  rw [hbits]
  by_cases hlt : ((C:Int)-p).toNat<C+m
  · rw [ite_eq_left hlt,testBit_pack]
    simp only [hlt,decide_true,Bool.true_and]
    congr 1
    omega
  · rw [ite_eq_right hlt]
    by_cases he : ((C:Int)-p).toNat=C+m
    · rw [he,Nat.sub_self]
      have hp' : p=-(m:Int) := by omega
      rw [hp',hx.1]
      decide
    · have hz := hx.2 p (by omega)
      rw [hz]
      have hne : ((C:Int)-p).toNat-(C+m)≠0 := by omega
      have hbit := Nat.testBit_bool_toNat true (((C:Int)-p).toNat-(C+m))
      simpa [hne] using hbit

theorem centered_orbit (a C t : Nat) :
    (orbit a t).testBit (C+t) = evol (centeredRow C a) t 0 := by
  rw [testBit_orbit]
  have hshift := Rule30ZeroBoundaryBarriers.evol_shift_all
    (x:=row a) (x':=centeredRow C a) (d:=(C:Int))
    (fun p => by unfold centeredRow; congr 1; omega) t (-(C:Int))
  rw [show -(C:Int)+(C:Int)=0 by omega] at hshift
  rw [hshift]
  congr 1
  omega

def signature (C a : Nat) : Nat → Nat
  | 0 => 0
  | H+1 => (a.testBit C).toNat ||| (signature (C+1) (Phi a) H <<< 1)

theorem orbit_start_Phi (a : Nat) : ∀ t, orbit (Phi a) t = orbit a (t+1)
  | 0 => rfl
  | t+1 => by simp only [orbit,orbit_start_Phi a t]

theorem signature_eq {C a b H : Nat}
    (h : ∀ t, t<H → (orbit a t).testBit (C+t) = (orbit b t).testBit (C+t)) :
    signature C a H = signature C b H := by
  induction H generalizing C a b with
  | zero => rfl
  | succ H ih =>
    have hzero := h 0 (by omega)
    simp only [orbit,Nat.add_zero] at hzero
    rw [signature,signature,hzero]
    have htail : signature (C+1) (Phi a) H = signature (C+1) (Phi b) H :=
      ih (fun t ht => by
        rw [orbit_start_Phi,orbit_start_Phi]
        have he := h (t+1) (by omega)
        simpa only [show C+1+t=C+(t+1) by omega] using he)
    rw [htail]

/-- All signatures of a dyadic interval, enumerated as a binary tree. -/
noncomputable def allSignatures (H C : Nat) : Nat → Nat → Nat
  | 0,a => Nat.shiftLeft 1 (signature C a H)
  | B+1,a => Nat.lor (allSignatures H C B a) (allSignatures H C B (a+2^B))

theorem member_allSignatures (H C : Nat) : ∀ B a r, r<2^B →
    (allSignatures H C B a).testBit (signature C (a+r) H) = true
  | 0,a,r,hr => by
    have he : r=0 := by simpa using hr
    subst he
    simp only [Nat.add_zero,allSignatures,Nat.shiftLeft_eq',Nat.one_shiftLeft]
    exact Nat.testBit_two_pow_self
  | B+1,a,r,hr => by
    rw [allSignatures,Nat.lor_eq,Nat.testBit_or]
    by_cases hlt : r<2^B
    · rw [member_allSignatures H C B a r hlt]
      rfl
    · have hr' : r-2^B<2^B := by
        rw [Nat.pow_succ] at hr
        omega
      have hm := member_allSignatures H C B (a+2^B) (r-2^B) hr'
      rw [show a+2^B+(r-2^B)=a+r by omega] at hm
      rw [hm]
      simp

noncomputable def edgeSignatures (H m : Nat) : Nat :=
  allSignatures H (H-1) (H-1+m) (2^(H-1+m))

theorem actual_signature {x : Int → Bool} {m H : Nat} (hH : 0<H)
    (hx : HasLeftEdge x (-(m:Int))) :
    ∃ a, (edgeSignatures H m).testBit (signature (H-1) a H) = true ∧
      ∀ t, t<H → (orbit a t).testBit (H-1+t) = evol x t 0 := by
  let C:=H-1
  let B:=C+m
  let low:=pack x C B
  let a:=2^B+low
  refine ⟨a,member_allSignatures H C B (2^B) low (pack_lt x C B),?_⟩
  intro t ht
  rw [centered_orbit]
  have hlocal := Rule30ZeroBoundaryBarriers.evol_local_le
    (x:=x) (x':=centeredRow C a) (d:=0) (b:=(C:Int))
    (fun p hp => by simpa using centered_row_agrees hx p hp) t 0 (by dsimp [C]; omega)
  simpa using hlocal

/-- Generic soundness. The checked mask equality is the only computational
certificate; no SAT solver or native decision procedure is a proof oracle. -/
theorem no_common_trace_prefix {H m n : Nat} (hH : 0<H)
    (certificate : Nat.land (edgeSignatures H m) (edgeSignatures H n) = 0)
    {x y : Int → Bool} (hx : HasLeftEdge x (-(m:Int))) (hy : HasLeftEdge y (-(n:Int))) :
    ¬ (∀ t, t<H → evol x t 0 = evol y t 0) := by
  intro htrace
  obtain ⟨a,ha,hax⟩ := actual_signature hH hx
  obtain ⟨b,hb,hby⟩ := actual_signature hH hy
  have heq : signature (H-1) a H = signature (H-1) b H := signature_eq fun t ht => by
    rw [hax t ht,hby t ht,htrace t ht]
  rw [← heq] at hb
  have hm : (Nat.land (edgeSignatures H m) (edgeSignatures H n)).testBit
      (signature (H-1) a H) = true := by rw [Nat.land_eq,Nat.testBit_and,ha,hb]; rfl
  rw [certificate] at hm
  simp at hm

set_option maxHeartbeats 0 in
theorem certificate_zero_one : Nat.land (edgeSignatures 2 0) (edgeSignatures 2 1) = 0 := by decide

set_option maxHeartbeats 0 in
theorem certificate_zero_two : Nat.land (edgeSignatures 3 0) (edgeSignatures 3 2) = 0 := by decide

set_option maxHeartbeats 0 in
theorem certificate_one_two : Nat.land (edgeSignatures 9 1) (edgeSignatures 9 2) = 0 := by decide

theorem negative_self_control : Nat.land (edgeSignatures 3 1) (edgeSignatures 3 1) ≠ 0 := by decide

/-- An unconditional base case for the open global question. Right halves
are arbitrary, possibly infinite; only the left-edge positions are bounded. -/
theorem separate_minus_one_minus_two {x y : Int → Bool}
    (hx : HasLeftEdge x (-1)) (hy : HasLeftEdge y (-2)) :
    ¬ (∀ t, t<9 → evol x t 0 = evol y t 0) :=
  no_common_trace_prefix (H:=9) (m:=1) (n:=2) (by decide) certificate_one_two hx hy

end Ruliology.CellularAutomata.Rule30TraceSeparationResearch
