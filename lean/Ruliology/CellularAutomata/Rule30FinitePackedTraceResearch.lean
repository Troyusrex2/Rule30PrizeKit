module

public import Ruliology.CellularAutomata.Rule30ThreeConeResearch
public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

/-!
# Sound finite packed realization of arbitrary temporal prefixes

For any right half and desired center trace, use the catalog's forced
left-neighbor column and the packed inverse to construct the first N left
cells. The rest of the left half is white. The actual center agrees with
the requested trace through time N; a bounded right half gives a finite
whole configuration. This certifies the structured adversarial starts used
to falsify proposed ranks. It proves no infinite periodic finite start.

The realization and locality principles are existing catalog results; this
module connects the explicit finite packed constructor to them. No priority
or prize solution is claimed.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30FinitePackedTraceResearch

open Rule30Jen Rule30Realization Rule30ZeroBoundaryBarriers
open Rule30ThreeConeResearch Rule30PackedReconstructionResearch
open Rule30PeriodTwoSideways (FinConfig)

theorem lc_eq_recon (R : Int → Bool) (c : Nat → Bool) : ∀ k t,
    lc R c k t=recon c (ycol R c) k t := by
  have key : ∀ k : Nat,
      (∀ t, lc R c k t=recon c (ycol R c) k t) ∧
      (∀ t, lc R c (k+1) t=recon c (ycol R c) (k+1) t) := by
    intro k
    induction k with
    | zero => exact ⟨fun _ => rfl,fun _ => rfl⟩
    | succ k ih =>
        refine ⟨ih.2,fun t => ?_⟩
        rw [lc,recon_two,ih.2 (t+1),ih.2 t,ih.1 t]
  exact fun k t => (key k).1 t

noncomputable def packedConf (R : Int → Bool) (c : Nat → Bool) (N : Nat)
    (p : Int) : Bool :=
  if 1≤p then R p else if p=0 then c 0 else
    if -(N:Int)≤p then
      (advance ((-p).toNat-1) (pack c N) (pack (ycol R c) N)).2.testBit 0
    else false

theorem packedConf_right (R : Int → Bool) (c : Nat → Bool) (N : Nat)
    (p : Int) (hp : 1≤p) : packedConf R c N p=R p := by
  simp [packedConf,hp]

theorem packedConf_center (R : Int → Bool) (c : Nat → Bool) (N : Nat) :
    packedConf R c N 0=c 0 := by simp [packedConf]

theorem packedConf_white (R : Int → Bool) (c : Nat → Bool) (N : Nat)
    (p : Int) (hp : p< -(N:Int)) : packedConf R c N p=false := by
  simp [packedConf,show ¬1≤p by omega,show p≠0 by omega,show ¬-(N:Int)≤p by omega]

theorem packedConf_depth (R : Int → Bool) (c : Nat → Bool) (N k : Nat) (hk : k<N) :
    packedConf R c N (-((k+1:Nat):Int))=
      (advance k (pack c N) (pack (ycol R c) N)).2.testBit 0 := by
  unfold packedConf
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by omega)]
  simp

/-- The computed finite row equals the full catalog realization everywhere
at or right of the truncation point, for arbitrary N and arbitrary profiles. -/
theorem packedConf_agrees (R : Int → Bool) (c : Nat → Bool) (N : Nat)
    (p : Int) (hp : -(N:Int)≤p) : packedConf R c N p=conf R c p := by
  by_cases hpos : 1≤p
  · simp [packedConf,conf,hpos]
  · by_cases hz : p=0
    · subst p; simp [packedConf,conf,lc]
    · have hneg : p<0 := by omega
      obtain ⟨k,hk⟩ : ∃ k : Nat, p= -((k+1:Nat):Int) :=
        ⟨(-p).toNat-1,by omega⟩
      subst p
      have hkn : k<N := by omega
      rw [packedConf_depth R c N k hkn]
      have h := Rule30ThreeConeResearch.packed_sound (pack c N) (pack (ycol R c) N)
        N c (ycol R c)
        (fun t ht => by simp [pack_bit,ht])
        (fun t ht => by simp [pack_bit,ht]) k 0 (by omega)
      unfold conf
      rw [ite_eq_right (by omega)]
      simpa only [Int.neg_neg,Int.toNat_natCast,lc_eq_recon] using h.2

/-- The actual whole-line evolution realizes every requested observation
through time N. There is no bound on N or assumption about later behavior. -/
theorem packedConf_trace (R : Int → Bool) (c : Nat → Bool) (N t : Nat) (ht : t≤N) :
    evol (packedConf R c N) t 0=c t := by
  have h := evol_local_ge (x:=conf R c) (x':=packedConf R c N) (d:=0) (a:= -(N:Int))
    (fun p hp => by simpa using packedConf_agrees R c N p hp) t 0 (by omega)
  simpa using h.trans ((realize R c).2 t)

theorem packedConf_finite (R : Int → Bool) (c : Nat → Bool) (N W : Nat)
    (hR : ∀ p : Int, (W:Int)<p → R p=false) : FinConfig (packedConf R c N) := by
  refine ⟨N+W,fun p hp => ?_⟩
  by_cases hleft : p< -(N:Int)
  · exact packedConf_white R c N p hleft
  · have hright : (W:Int)<p := by omega
    have hpos : 1≤p := by omega
    rw [packedConf_right R c N p hpos,hR p hright]

/-- An explicit finite constructor for every center prefix and every fixed
bounded right half. This is finite-prefix realization, not a periodic tail. -/
theorem finite_prefix_constructor (R : Int → Bool) (c : Nat → Bool) (N W : Nat)
    (hR : ∀ p : Int, (W:Int)<p → R p=false) :
    FinConfig (packedConf R c N) ∧
      (∀ p, 1≤p → packedConf R c N p=R p) ∧
      ∀ t, t≤N → evol (packedConf R c N) t 0=c t :=
  ⟨packedConf_finite R c N W hR,packedConf_right R c N,
    fun t ht => packedConf_trace R c N t ht⟩

def altTrace (t : Nat) : Bool := decide (t%2=0)
def emptyRight (_ : Int) : Bool := false

theorem finite_alternating_prefix (N : Nat) :
    FinConfig (packedConf emptyRight altTrace N) ∧
      ∀ t, t≤N → evol (packedConf emptyRight altTrace N) t 0=decide (t%2=0) :=
  ⟨packedConf_finite emptyRight altTrace N 0 (fun _ _ => rfl),
    fun t ht => packedConf_trace emptyRight altTrace N t ht⟩

end Ruliology.CellularAutomata.Rule30FinitePackedTraceResearch
