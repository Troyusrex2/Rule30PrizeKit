import SafeClockEntry
import Rule30EvenModeRigidityResearch

/-! Uniform even-clock lifting near an actual returning prefix. If at most
three cells are appended to a finite-white P-returning word, and the newest
trace of the result is P-periodic, then the WHOLE result returns at P.
P is any positive even natural number. No Safe or low-height premise occurs.
The full arbitrary-distance column-to-whole-word lifting problem is not
claimed. The proof consumes the existing even-plateau OR rigidity theorem. -/
namespace EvenClockLifting
open CedarSafetySoundness CedarSafety HeightOneLogic HeightOneSemantics
open HeightOneTransfer RootEventHeight
open Rule30ClockJetResearch Rule30ClockModeResearch Rule30EvenModeRigidityResearch
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem drop_snoc (xs : List Bool) (b : Bool) : (xs++[b]).dropLast=xs := by
  simp

theorem old_eq_previous (xs : List Bool) : old xs=tr xs.dropLast := by
  by_cases hz : xs=[]
  · subst xs;rfl
  obtain ⟨u,v,rfl⟩ := split_last xs (List.length_pos_iff.mpr hz)
  simp only [old_snoc,drop_snoc]

/-- Uniform actual predecessor recurrence, including the empty white prefix. -/
theorem trace_recurrence (xs : List Bool) :
    Recurrence (tr xs.dropLast) (tr xs.dropLast.dropLast) (tr xs) := by
  by_cases hz : xs=[]
  · subst xs
    intro t
    change RootShortExtensionCore.lift8 zero (t+1)=
      xor (RootShortExtensionCore.lift8 zero t)
        (RootShortExtensionCore.lift8 zero t || RootShortExtensionCore.lift8 zero t)
    simp only [RootShortExtensionCore.lift8_zero]
    rfl
  obtain ⟨u,v,rfl⟩ := split_last xs (List.length_pos_iff.mpr hz)
  intro t
  simp only [drop_snoc]
  rw [← old_eq_previous u,tr_snoc,RootShortExtensionCore.history]

/-- A repeating newest column gives precisely the OR-alias relation on its
two actual parents. This does not by itself give either parent's period. -/
theorem periodic_forcing (a u b : Nat → Bool) (P : Nat)
    (hr : Recurrence a u b) (hp : Periodic b P) :
    ∀ t, (a (t+P) || u (t+P))=(a t || u t) := by
  intro t
  have h0 := hr t
  have hP := hr (t+P)
  rw [show t+P+1=(t+1)+P by omega,hp (t+1),hp t] at hP
  have cancel : ∀ x a b : Bool, xor x a=xor x b → a=b := by decide +kernel
  exact cancel _ _ _ (hP.symm.trans h0)

theorem anti_xor (h : Nat → Bool) (P : Nat)
    (ha : ∀ t, h (t+P)=!h t) : ∀ t, h (t+P)=xor (h t) true := by
  intro t
  rw [ha t]
  cases h t <;> rfl

/-- The first anti-P column cannot be hidden by the immediately newer cell
at an even P. No period assumption is made on any later column. -/
theorem no_drop_one (g h k l : Nat → Bool) (P : Nat) (he : Even P)
    (gs : Recurrence h k g) (hs : Recurrence k l h)
    (ha : ∀ t, h (t+P)=!h t) (hk : Periodic k P) : ¬ Periodic g P := by
  intro hg
  have ho := periodic_forcing h k g P gs hg
  have hall (t : Nat) : k t=true := by
    have h0 := ho t
    rw [ha t,hk t] at h0
    have gate : ∀ h k : Bool, ((!h) || k)=(h || k) → k=true := by decide +kernel
    exact gate _ _ h0
  have hflip (t : Nat) : h (t+1)=xor (h t) true := by
    rw [hs t,hall t,Bool.true_or]
  obtain ⟨n,hn⟩ := he
  have hp : P=2*n := by omega
  have hret := even_flip_return h hflip n 0
  simp only [Nat.zero_add] at hret
  rw [← hp] at hret
  have hanti := ha 0
  simp only [Nat.zero_add,hret] at hanti
  have bad : ∀ b : Bool, b ≠ !b := by decide +kernel
  exact bad _ hanti

/-- Local consumer of the previously verified even-plateau rigidity. The
actual recurrences for k and its two predecessors are retained explicitly. -/
theorem no_drop_two (z g h k l m : Nat → Bool) (P : Nat) (he : Even P)
    (zs : Recurrence g h z) (gs : Recurrence h k g)
    (hs : Recurrence k l h) (ks : Recurrence l m k)
    (ha : ∀ t, h (t+P)=!h t) (hk : Periodic k P) : ¬ Periodic z P := by
  intro hz
  have hor := periodic_forcing g h z P zs hz
  have hanti := anti_xor h P ha
  have hconst := periodic_or_with_anti_mask g h P hanti hor
  have hg2 := constant_or_forces_double_period g h k P gs hanti hk hconst
  let q := delta g P
  have hq : ∀ t, q (t+1)=xor (q t) (!k t) := shift_difference_step g h k P gs hanti hk
  have hqp : ∀ t, q (t+P)=q t := mode_periodic g P hg2
  have ho : ∀ t, (q t || (!k t && !l t))=true := by
    intro t
    have hread := lower_readout_eq g h k l P gs hs hanti hk t
    rw [← hread]
    simp only [lowerReadout,delta,orTrace,hconst]
    rfl
  obtain ⟨n,hn⟩ := he
  have hp : P=2*n := by omega
  exact even_constant_mode_impossible q h k l m n hq hs ks
    (by intro t;rw [← hp];exact hqp t)
    (by intro t;rw [← hp];exact hanti t) ho

theorem return_one (u : List Bool) (a : Bool) (P : Nat)
    (hu : evolution P u=u) (hp : Periodic (tr (u++[a])) P) :
    evolution P (u++[a])=u++[a] := by
  have h := hp 0
  simp only [Nat.zero_add] at h
  have hi : tr (u++[a]) 0=a := by rw [tr_snoc];rfl
  rw [hi] at h
  rw [evolution_snoc,hu,h]

theorem return_two (u : List Bool) (a b : Bool) (P : Nat) (he : Even P)
    (hu : evolution P u=u) (hp : Periodic (tr ((u++[a])++[b])) P) :
    evolution P ((u++[a])++[b])=(u++[a])++[b] := by
  by_cases hr : evolution P (u++[a])=u++[a]
  · exact return_one (u++[a]) b P hr hp
  · have ha := SafeClockEntry.nonreturn_leaf_antiperiod u a P hu hr
    have hs := trace_recurrence (u++[a])
    have gs := trace_recurrence ((u++[a])++[b])
    simp only [drop_snoc] at hs gs
    exact False.elim (no_drop_one _ _ _ _ P he gs hs ha (trace_period_of_return u P hu) hp)

theorem return_three (u : List Bool) (a b c : Bool) (P : Nat) (he : Even P)
    (hu : evolution P u=u) (hp : Periodic (tr (((u++[a])++[b])++[c])) P) :
    evolution P (((u++[a])++[b])++[c])=((u++[a])++[b])++[c] := by
  by_cases hr : evolution P (u++[a])=u++[a]
  · exact return_two (u++[a]) b c P he hr hp
  · have ha := SafeClockEntry.nonreturn_leaf_antiperiod u a P hu hr
    have hs := trace_recurrence (u++[a])
    have gs := trace_recurrence ((u++[a])++[b])
    have zs := trace_recurrence (((u++[a])++[b])++[c])
    simp only [drop_snoc] at hs gs zs
    exact False.elim (no_drop_two _ _ _ _ _ _ P he zs gs hs (trace_recurrence u)
      ha (trace_period_of_return u P hu) hp)

/-- Arbitrary spatial width and arbitrary positive EVEN P. The only supplied
whole-word return belongs to u. The child supplies solely its newest trace's
P-periodicity; no Safe, height, or child whole-clock premise is required. -/
theorem short_extension_clock_lifting (u v : List Bool) (P : Nat) (_hP : 0<P)
    (he : Even P) (hu : evolution P u=u) (hv : v.length≤3)
    (hp : Periodic (tr (u++v)) P) : evolution P (u++v)=u++v := by
  cases v with
  | nil => simpa using hu
  | cons a v =>
    cases v with
    | nil => exact return_one u a P hu hp
    | cons b v =>
      cases v with
      | nil =>
        have h := return_two u a b P he hu
        simp only [List.append_assoc,List.cons_append,List.nil_append] at h
        exact h hp
      | cons c v =>
        cases v with
        | nil =>
          have h := return_three u a b c P he hu
          simp only [List.append_assoc,List.cons_append,List.nil_append] at h
          exact h hp
        | cons d vs => simp at hv

end EvenClockLifting
