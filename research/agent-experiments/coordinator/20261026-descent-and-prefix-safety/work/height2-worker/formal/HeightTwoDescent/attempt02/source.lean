import HeightTwoNearReturn
import HeightOneSemantics

/-! A genuine height-two column with a coSafe immediate ancestor yields a
strictly shorter Safe word that fails whole-word return8.  The residual
minimality statement retains both actual ancestors and does not identify a
column period with a whole-prefix clock. -/
namespace HeightTwoDescent
open CedarSafetySoundness CedarSafety HeightOneSemantics HeightTwoNearReturn
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def CoSafe (xs : List Bool) : Prop :=
  ∀ t, ¬ (tr xs t=true ∧ tr xs (t+1)=true)

def NonEight (xs : List Bool) : Prop :=
  ¬ ∀ t, tr xs (t+8)=tr xs t

/-- This is an explicit minimality hypothesis about Safe words, not a
consequence of minimal width among height-two words. -/
def NoShorterSafeFailure (xs : List Bool) : Prop :=
  ∀ ys : List Bool, ys.length<xs.length → Safe ys → evolution 8 ys=ys

theorem trace_function (xs : List Bool) :
    tr xs=(fun t => newest (evolution t xs)) := funext (trace_eq xs)

theorem height_eq_WH (b : Nat → Bool) (t : Nat) :
    whiteHeight b t=HeightOneLogic.WH b t := whiteHeight_eq b t

/-- A closed positive even temporal period supplies the all-time height band.
The period belongs only to the newest column; it is not used as a prefix clock. -/
theorem span_two_of_closed_period (b : Nat → Bool) (P : Nat)
    (hP : 0<P) (he : Even P) (hp : HeightOneLogic.Periodic b P)
    (hc : whiteHeight b P=0)
    (hr : ∃ lo : Int, ∀ t, t≤P → lo≤whiteHeight b t ∧ whiteHeight b t≤lo+2) :
    SpanTwo b := by
  obtain ⟨lo,hr⟩ := hr
  refine ⟨lo,?_⟩
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      by_cases ht : t≤P
      · exact hr t ht
      · have ht' : t-P<t := by omega
        have hw := HeightOneLogic.height_shift_period b P he hp (t-P)
        simp only [← height_eq_WH] at hw
        rw [show P+(t-P)=t by omega,hc,zero_add] at hw
        rw [hw]
        exact ih (t-P) ht'

theorem flip_safe (xs : List Bool) (a : Bool) (hc : CoSafe (xs++[a])) :
    Safe (xs++[!a]) := by
  intro t ht
  have h0 : Bool.not (tr (xs++[a]) t)=false := by
    rw [← leaf_flip_trace,trace_eq]
    exact ht.1
  have h1 : Bool.not (tr (xs++[a]) (t+1))=false := by
    rw [← leaf_flip_trace,trace_eq]
    exact ht.2
  have e0 : tr (xs++[a]) t=true := by simpa using h0
  have e1 : tr (xs++[a]) (t+1)=true := by simpa using h1
  exact hc t ⟨e0,e1⟩

/-- A coSafe ancestor one or two actual spatial cells back gives a strictly
shorter Safe/nonreturn8 word by flipping that ancestor's newest initial bit. -/
theorem coSafe_parent_descent (xs : List Bool) (a : Bool) (tail : List Bool)
    (htail : 0<tail.length) (hlen : tail.length≤2)
    (hh : SpanTwo (tr ((xs++[a])++tail)))
    (hn : NonEight ((xs++[a])++tail)) (hc : CoSafe (xs++[a])) :
    Safe (xs++[!a]) ∧ evolution 8 (xs++[!a])≠xs++[!a] ∧
      (xs++[!a]).length<((xs++[a])++tail).length := by
  refine ⟨flip_safe xs a hc,?_,?_⟩
  · intro hret
    have hu := (leaf_flip_return xs a 8).mp hret
    have hh' := hh
    rw [trace_function] at hh'
    have hn' := hn
    unfold NonEight at hn'
    rw [trace_function] at hn'
    exact no_near_return_prefix (xs++[a]) tail hlen hh' hn' hu
  · simp only [List.length_append,List.length_singleton]
    omega

theorem closed_period_coSafe_descent (xs : List Bool) (a : Bool) (tail : List Bool)
    (htail : 0<tail.length) (hlen : tail.length≤2)
    (P : Nat) (hP : 0<P) (he : Even P)
    (hp : HeightOneLogic.Periodic (tr ((xs++[a])++tail)) P)
    (hc : whiteHeight (tr ((xs++[a])++tail)) P=0)
    (hr : ∃ lo : Int, ∀ t, t≤P →
      lo≤whiteHeight (tr ((xs++[a])++tail)) t ∧
      whiteHeight (tr ((xs++[a])++tail)) t≤lo+2)
    (hn : NonEight ((xs++[a])++tail)) (ha : CoSafe (xs++[a])) :
    Safe (xs++[!a]) ∧ evolution 8 (xs++[!a])≠xs++[!a] ∧
      (xs++[!a]).length<((xs++[a])++tail).length :=
  coSafe_parent_descent xs a tail htail hlen
    (span_two_of_closed_period _ P hP he hp hc hr) hn ha

theorem minimal_counterexample_parent (xs : List Bool) (a : Bool) (tail : List Bool)
    (htail : 0<tail.length) (hlen : tail.length≤2)
    (hh : SpanTwo (tr ((xs++[a])++tail)))
    (hn : NonEight ((xs++[a])++tail))
    (hm : NoShorterSafeFailure ((xs++[a])++tail)) : ¬ CoSafe (xs++[a]) := by
  intro hc
  obtain ⟨hs,hr,hl⟩ := coSafe_parent_descent xs a tail htail hlen hh hn hc
  exact hr (hm _ hl hs)

/-- Under the stated Safe-word minimality hypothesis, both nonempty immediate
ancestors of the height-two/non-eight column must have a temporal 11 pair. -/
theorem minimal_counterexample_parents (xs : List Bool) (a b c : Bool)
    (hh : SpanTwo (tr (xs++[a,b,c]))) (hn : NonEight (xs++[a,b,c]))
    (hm : NoShorterSafeFailure (xs++[a,b,c])) :
    ¬ CoSafe (xs++[a,b]) ∧ ¬ CoSafe (xs++[a]) := by
  constructor
  · have h := minimal_counterexample_parent (xs++[a]) b [c] (by simp) (by simp)
    simp only [List.append_assoc,List.cons_append,List.nil_append] at h
    exact h hh hn hm
  · have h := minimal_counterexample_parent xs a [b,c] (by simp) (by simp)
    simp only [List.append_assoc,List.cons_append,List.nil_append] at h
    exact h hh hn hm

theorem not_coSafe_iff_pair (xs : List Bool) :
    ¬ CoSafe xs ↔ ∃ t, tr xs t=true ∧ tr xs (t+1)=true := by
  classical
  simp only [CoSafe,not_forall,not_not]

end HeightTwoDescent
