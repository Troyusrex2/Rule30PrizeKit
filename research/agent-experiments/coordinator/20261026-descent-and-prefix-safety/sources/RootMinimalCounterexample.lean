import RootReturningPrefixSafety
import HeightOneTransfer

/-! A minimal-width Safe nonreturning word has both temporal 00 and 11
in each prefix within three cells of its newest end. This uses the stronger
returning-prefix extension theorem, not safety of the original prefix. -/
namespace RootMinimalCounterexample
open CedarSafetySoundness CedarSafety HeightOneSemantics
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def CoSafe (xs : List Bool) : Prop := ∀ t,
  ¬ (newest (evolution t xs)=true ∧ newest (evolution (t+1) xs)=true)

theorem flipped_safe (xs : List Bool) (v : Bool) (hc : CoSafe (xs++[v])) :
    Safe (xs++[!v]) := by
  intro t bad
  apply hc t
  have h0 : (!tr (xs++[v]) t)=false := by
    simpa only [← trace_eq,leaf_flip_trace] using bad.1
  have h1 : (!tr (xs++[v]) (t+1))=false := by
    simpa only [← trace_eq,leaf_flip_trace] using bad.2
  have localFact : ∀ x : Bool, (!x)=false → x=true := by decide +kernel
  rw [← trace_eq,← trace_eq]
  exact ⟨localFact _ h0,localFact _ h1⟩

theorem coSafe_returns_of_shorter_completeness (xs : List Bool) (N : Nat)
    (hlen : xs.length<N) (hc : CoSafe xs)
    (hshort : ∀ ys : List Bool, ys.length<N → Safe ys → evolution 8 ys=ys) :
    evolution 8 xs=xs := by
  by_cases h0 : xs=[]
  · subst xs; rfl
  have hp : 0<xs.length := List.length_pos_iff.mpr h0
  obtain ⟨ys,v,rfl⟩ := HeightOneTransfer.split_last xs hp
  have hsf := flipped_safe ys v hc
  have hl : (ys++[!v]).length<N := by simpa using hlen
  exact (leaf_flip_return ys v 8).mp (hshort (ys++[!v]) hl hsf)

theorem near_prefix_nonreturn (u v : List Bool) (hv : v.length≤3)
    (hs : Safe (u++v)) (hr : evolution 8 (u++v)≠u++v) : evolution 8 u≠u := by
  intro hu
  exact hr (RootReturningPrefixSafety.returning_prefix_safe_extension u v hu hv hs)

theorem near_prefix_both_events (u v : List Bool)
    (hvpos : 0<v.length) (hv : v.length≤3)
    (hs : Safe (u++v)) (hr : evolution 8 (u++v)≠u++v)
    (hshort : ∀ ys : List Bool, ys.length<(u++v).length → Safe ys → evolution 8 ys=ys) :
    (∃ t, newest (evolution t u)=false ∧ newest (evolution (t+1) u)=false) ∧
    (∃ t, newest (evolution t u)=true ∧ newest (evolution (t+1) u)=true) := by
  have hl : u.length<(u++v).length := by simp only [List.length_append];omega
  have hnr := near_prefix_nonreturn u v hv hs hr
  have hns : ¬ Safe u := fun hu => hnr (hshort u hl hu)
  have hnc : ¬ CoSafe u := fun hu =>
    hnr (coSafe_returns_of_shorter_completeness u (u++v).length hl hu hshort)
  constructor
  · by_contra hn
    apply hns
    intro t bad
    exact hn ⟨t,bad⟩
  · by_contra hn
    apply hnc
    intro t bad
    exact hn ⟨t,bad⟩

end RootMinimalCounterexample
