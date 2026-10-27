module
public import Rule30CAClockDemodulationResearch

/-! A gated two-cell extension cannot add a clock birth at its last pair.
The older whole return is supplied, and no gate inheritance is asserted. -/
@[expose] public section
namespace Rule30CAGateReturnResearch
open Rule30CommonPastResearch Rule30ReaderCanonicalResearch Rule30CAObserverResearch
open Rule30AnchoredConstantResearch Rule30CAClockDemodulationResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def Gated (u : List Bool) (g h : Bool) : Prop :=
  ∀ t, outR (u++[g,h]) t = !(giter u g t) ∧ outS (u++[g,h]) t=true

theorem not_constant_outputs (u : List Bool) (hu : u≠[]) (b : Bool) :
    ¬ ∀ t, outR u t=b ∧ outS u t=b := by
  intro hc
  have ht : ∀ t, trace (word0 u) t=b := by
    intro t
    have hr := Nat.mod_lt t (by decide : 0<2)
    by_cases hm : t%2=0
    · have he : t=2*(t/2) := by omega
      rw [he,trace_even]
      exact (hc _).1
    · have he : t=2*(t/2)+1 := by omega
      rw [he,trace_odd hu]
      exact (hc _).2
  have hn : 0<(word0 u).length := by simp [word0]
  apply no_constant_after_black (full (word0 u)) (full_actual _) (word0_first_black u)
    ((word0 u).length-1) (by simp [word0]) b
  intro t
  rw [← trace_full _ hn]
  exact ht t

theorem cancel_gate_R (a b : Bool) :
    xor (xor (!a) true) (xor (!b) true)=xor a b := by
  cases a <;> cases b <;> rfl
theorem cancel_gate_S (a b : Bool) :
    xor (xor true (!a)) (xor true (!b))=xor a b := by
  cases a <;> cases b <;> rfl

theorem gated_no_birth (u : List Bool) (g h : Bool) (P : Nat)
    (hu : u≠[]) (hp : titer u P=u) (hg : Gated u g h) :
    birth P u g=false := by
  cases hb : birth P u g with
  | false => rfl
  | true =>
      exfalso
      apply not_constant_outputs u hu false
      intro t
      have hR : demodR P (u++[g,h]) t=true := by
        dsimp only [demodR,delta]
        rw [(hg (t+P)).1,(hg (t+P)).2,(hg t).1,(hg t).2,cancel_gate_R]
        exact (g_displacement u g P hp t).trans hb
      have hS : demodS P (u++[g,h]) t=true := by
        dsimp only [demodS,delta]
        rw [(hg (t+P)).2,(hg (t+P+1)).1,(hg t).2,(hg (t+1)).1,cancel_gate_S]
        rw [show t+P+1=t+1+P by omega]
        exact (g_displacement u g P hp (t+1)).trans hb
      have hm := masked_demodulation u g h P hu hp t
      rw [hR,hS,hb] at hm
      constructor
      · cases hr : outR u t with
        | false => rfl
        | true =>
            have hh := hm.1
            rw [hr] at hh
            cases hh
      · cases hs : outS u t with
        | false => rfl
        | true =>
            have hh := hm.2
            rw [hs] at hh
            cases hh

/-- A supplied whole return of the older nonempty prefix is already a whole
return of the gated extension. No gate property of the prefix is assumed. -/
theorem gated_return (u : List Bool) (g h : Bool) (P : Nat)
    (hu : u≠[]) (hp : titer u P=u) (hg : Gated u g h) :
    titer (u++[g,h]) P=u++[g,h] := by
  have he := gated_no_birth u g h P hu hp hg
  rw [birth_eq] at he
  have hgp : giter u g P=g := by
    cases hgP : giter u g P <;> cases g <;> simp_all
  have hinit : h= !g := by
    have hi := (hg 0).1
    simpa only [outR,titer,giter,r,last_append_two] using hi
  obtain ⟨b,hb⟩ := titer_append_two u g h hu P
  have hlast := (hg P).1
  unfold outR at hlast
  rw [hb] at hlast
  unfold r at hlast
  rw [last_append_two] at hlast
  rw [hgp] at hlast
  have hbh : b=h := hlast.trans hinit.symm
  rw [hb,hp,hgp,hbh]

end Rule30CAGateReturnResearch
