import HeightOnePeriodicity
import RootAntiPeriodHeight
import RootReturningPrefixSafety

/-! A Safe last cell never enlarges an even whole-prefix clock. A clock
increase across the last TWO cells therefore supplies a genuine height-two
ancestor. The unresolved alternative is equality of whole-prefix clocks. -/
namespace SafeClockEntry
open CedarSafetySoundness CedarSafety HeightOneLogic HeightOneSemantics
open HeightOneTransfer HeightOnePeriodicity
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def SpanTwo (b : Nat → Bool) : Prop :=
  ∃ lo : Int, ∀ t, lo≤WH b t ∧ WH b t≤lo+2

theorem not_safe_even_antiperiod (x : Nat → Bool) (P : Nat) (he : Even P)
    (ha : ∀ t, x (t+P)=!x t) : ¬ RootEventHeight.Safe x := by
  intro hs
  have h11 (t : Nat) : ¬ (x t=true ∧ x (t+1)=true) := by
    intro h
    apply hs (t+P)
    rw [ha t,show t+P+1=(t+1)+P by omega,ha (t+1),h.1,h.2]
    exact ⟨rfl,rfl⟩
  have localFact : ∀ a b c : Bool,
      ¬(a=false ∧ b=false) → ¬(a=true ∧ b=true) →
      ¬(b=false ∧ c=false) → ¬(b=true ∧ c=true) → c=a := by decide +kernel
  have htwo (t : Nat) : x (t+2)=x t :=
    localFact _ _ _ (hs t) (h11 t) (hs (t+1)) (h11 (t+1))
  have hiter (k t : Nat) : x (t+2*k)=x t := by
    induction k with
    | zero => rfl
    | succ k ih => rw [show t+2*(k+1)=(t+2*k)+2 by omega,htwo,ih]
  obtain ⟨k,hk⟩ := he
  have hret : x P=x 0 := by simpa [hk,show k+k=2*k by omega] using hiter k 0
  have hanti := ha 0
  simp only [Nat.zero_add,hret] at hanti
  cases hx : x 0 <;> simp [hx] at hanti

/-- This anti-period comes from a literal return of the WHOLE older prefix,
not from an asserted period of its newest coordinate. -/
theorem nonreturn_leaf_antiperiod (u : List Bool) (v : Bool) (P : Nat)
    (hu : evolution P u=u) (hn : evolution P (u++[v])≠u++[v]) :
    ∀ t, tr (u++[v]) (t+P)=!tr (u++[v]) t := by
  have hbit : tr (u++[v]) P≠v := by
    intro hv
    apply hn
    rw [evolution_snoc,hu,hv]
  have hflip : tr (u++[v]) P=!v := by
    cases hv : tr (u++[v]) P <;> cases v <;> simp_all
  intro t
  have ht := trace_restart (u++[v]) P t
  rw [evolution_snoc,hu,hflip,leaf_flip_trace] at ht
  simpa only [Nat.add_comm] using ht.symm

/-- Uniform in every even P. The Safe extension retains that SAME whole
return clock, rather than merely the possible doubled clock. -/
theorem safe_extension_preserves_even_return (u : List Bool) (v : Bool) (P : Nat)
    (he : Even P) (hu : evolution P u=u) (hs : CedarSafety.Safe (u++[v])) :
    evolution P (u++[v])=u++[v] := by
  by_contra hn
  apply not_safe_even_antiperiod (tr (u++[v])) P he (nonreturn_leaf_antiperiod u v P hu hn)
  intro t bad
  apply hs t
  simpa only [trace_eq] using bad

theorem height_two_of_safe_antiperiod (b c d : Nat → Bool) (P : Nat) (he : Even P)
    (hb : ∀ t, b (t+P)=b t) (hc : ∀ t, c (t+P)=!c t)
    (hd : RootEventHeight.Recurrence b c d) (hs : RootEventHeight.Safe d) : SpanTwo b := by
  rcases RootEventHeight.q_cases d 0 with hq | hq
  · refine ⟨-2-RootEventHeight.height (RootEventHeight.zeroPair b c) P,?_⟩
    intro t
    have h0 := RootEventHeight.safe_marked_height_range b c d hd hs t
    have h1 := RootEventHeight.safe_marked_height_range b c d hd hs (t+P)
    have hi := RootAntiPeriodHeight.paired_height_identity b c P he hb hc t
    change WH b t=_ at hi
    rcases h0 with h0|h0 <;> rcases h1 with h1|h1 <;> omega
  · refine ⟨-RootEventHeight.height (RootEventHeight.zeroPair b c) P,?_⟩
    intro t
    have h0 := RootEventHeight.safe_marked_height_range b c d hd hs t
    have h1 := RootEventHeight.safe_marked_height_range b c d hd hs (t+P)
    have hi := RootAntiPeriodHeight.paired_height_identity b c P he hb hc t
    change WH b t=_ at hi
    rcases h0 with h0|h0 <;> rcases h1 with h1|h1 <;> omega

theorem two_step_recurrence (u : List Bool) (c d : Bool) :
    RootEventHeight.Recurrence (tr u) (tr (u++[c])) (tr ((u++[c])++[d])) := by
  intro t
  rw [tr_snoc]
  rw [RootShortExtensionCore.history,old_snoc,Bool.or_comm]

/-- A whole-clock increase across two final cells derives the required
periodic/anti-periodic pair, instead of assuming that pair exists. -/
theorem safe_two_cell_clock_jump_height (u : List Bool) (c d : Bool) (P : Nat)
    (he : Even P) (hu : evolution P u=u)
    (hn : evolution P ((u++[c])++[d])≠(u++[c])++[d])
    (hs : CedarSafety.Safe ((u++[c])++[d])) : SpanTwo (tr u) := by
  have hc : evolution P (u++[c])≠u++[c] := by
    intro hc
    exact hn (safe_extension_preserves_even_return (u++[c]) d P he hc hs)
  apply height_two_of_safe_antiperiod (tr u) (tr (u++[c]))
    (tr ((u++[c])++[d])) P he (trace_period_of_return u P hu)
    (nonreturn_leaf_antiperiod u c P hu hc) (two_step_recurrence u c d)
  intro t bad
  apply hs t
  simpa only [trace_eq] using bad

/-- The actual two-cell ancestor also fails WHOLE F8 whenever the Safe
full word fails F8. No minimum-width assumption is needed for this entry. -/
theorem safe_clock_jump_entry (u : List Bool) (c d : Bool) (P : Nat)
    (he : Even P) (hu : evolution P u=u)
    (hn : evolution P ((u++[c])++[d])≠(u++[c])++[d])
    (hs : CedarSafety.Safe ((u++[c])++[d]))
    (h8 : evolution 8 ((u++[c])++[d])≠(u++[c])++[d]) :
    SpanTwo (tr u) ∧ evolution 8 u≠u := by
  refine ⟨safe_two_cell_clock_jump_height u c d P he hu hn hs,?_⟩
  intro hu8
  apply h8
  have hs' : CedarSafety.Safe (u++[c,d]) := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using hs
  have hr := RootReturningPrefixSafety.returning_prefix_safe_extension u [c,d] hu8 (by simp) hs'
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using hr

/-- Precise remaining alternative: if this actual ancestor is not height
two, EVERY even whole-return clock of it is already a clock of the Safe
full word. This is a whole-clock plateau, not an observer conclusion. -/
theorem safe_clock_plateau_of_not_height_two (u : List Bool) (c d : Bool)
    (hs : CedarSafety.Safe ((u++[c])++[d])) (hh : ¬ SpanTwo (tr u)) :
    ∀ P, Even P → evolution P u=u →
      evolution P ((u++[c])++[d])=(u++[c])++[d] := by
  intro P he hu
  by_contra hn
  exact hh (safe_two_cell_clock_jump_height u c d P he hu hn hs)

end SafeClockEntry
