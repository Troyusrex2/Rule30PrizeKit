import HeightOnePeriodicity

/-! Height-one descent for failure of WHOLE-word return8. A low-period
newest column does not hide a nonreturning prefix in this implication.
No global safety completeness is assumed. -/
namespace HeightOneDescent
open CedarSafetySoundness CedarSafety HeightOneLogic HeightOneSemantics
open HeightOneTransfer HeightOnePeriodicity
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem height_one_parent_safe_twins (xs : List Bool) (u a b : Bool)
    (hh : SpanOne (tr (((xs++[u])++[a])++[b]))) :
    CedarSafety.Safe ((xs++[u])++[!a]) ∧
      (∀ t, tr ((xs++[u])++[a]) t=tr (xs++[u]) t) ∧
      (∀ t, tr ((xs++[u])++[a]) t=D (tr (((xs++[u])++[a])++[b])) t) := by
  let B := tr (((xs++[u])++[a])++[b])
  let A := tr ((xs++[u])++[a])
  let U := tr (xs++[u])
  obtain ⟨P,hP,_,hp⟩ := exists_even_column_period (((xs++[u])++[a])++[b])
  have hi : ∀ t, ¬ (D B t=true ∧ D B (t+1)=true) :=
    isolated_derivative B hh (genuine_no11011 _) P hP hp
  have hb (t : Nat) : D B t=(A t || U t) := by
    change xor (tr (((xs++[u])++[a])++[b]) t)
      (tr (((xs++[u])++[a])++[b]) (t+1))=(A t || U t)
    rw [trace_step,old_snoc]
  have ha (t : Nat) : xor (A t) (A (t+1))=(U t || tr xs t) := by
    change xor (tr ((xs++[u])++[a]) t) (tr ((xs++[u])++[a]) (t+1))=(U t || tr xs t)
    rw [trace_step,old_snoc]
  have hu (t : Nat) : xor (U t) (U (t+1))=(tr xs t || old xs t) := trace_step xs u t
  obtain ⟨hA,hU⟩ := isolated_forces_twins B A U (tr xs) (old xs) hb ha hu hi
  refine ⟨?_,fun t => (hA t).trans (hU t).symm,hA⟩
  intro t bad
  have localFact : ∀ x : Bool, (!x)=false → x=true := by decide +kernel
  have h0 : (Bool.not (A t))=false := by
    simpa only [← trace_eq,leaf_flip_trace] using bad.1
  have h1 : (Bool.not (A (t+1)))=false := by
    simpa only [← trace_eq,leaf_flip_trace] using bad.2
  apply hi t
  rw [← hA t,← hA (t+1)]
  exact ⟨localFact _ h0,localFact _ h1⟩

theorem return8_of_flipped_parent_return (xs : List Bool) (u a b : Bool)
    (hh : SpanOne (tr (((xs++[u])++[a])++[b])))
    (hr : evolution 8 ((xs++[u])++[!a])=(xs++[u])++[!a]) :
    evolution 8 (((xs++[u])++[a])++[b])=((xs++[u])++[a])++[b] := by
  obtain ⟨_,ht,hd⟩ := height_one_parent_safe_twins xs u a b hh
  have hrA := (leaf_flip_return (xs++[u]) a 8).mp hr
  have htwo := return8_twins_two (xs++[u]) a hrA ht
  have hfour : Periodic (tr (((xs++[u])++[a])++[b])) 4 := by
    apply four_of_derivative_two
    intro t
    rw [← hd (t+2),← hd t]
    exact htwo t
  have h8 : tr (((xs++[u])++[a])++[b]) 8=b := by
    have h := (hfour 4).trans (hfour 0)
    rw [tr_snoc] at h ⊢
    exact h
  rw [evolution_snoc,hrA,h8]

theorem small_return8 (xs : List Bool) (hl : xs.length≤2) : evolution 8 xs=xs := by
  rw [show 8=4+4 by rfl,evolution_add,small_return4 xs hl,small_return4 xs hl]

/-- Failure of whole-word F8, not a claim about its newest column's least
period, is enough. The witness is the leaf-flipped immediate parent. -/
theorem height_one_nonreturn_shorter (xs : List Bool)
    (hh : SpanOne (tr xs)) (hn : evolution 8 xs≠xs) :
    ∃ ys : List Bool, ys.length+1=xs.length ∧ CedarSafety.Safe ys ∧ evolution 8 ys≠ys := by
  have hlen : 3≤xs.length := by
    by_contra h
    exact hn (small_return8 xs (by omega))
  obtain ⟨ps,b,hb⟩ := split_last xs (by omega)
  have hlps : 2≤ps.length := by rw [hb,List.length_append] at hlen;simp at hlen;omega
  obtain ⟨qs,a,ha⟩ := split_last ps (by omega)
  have hlqs : 1≤qs.length := by rw [ha,List.length_append] at hlps;simp at hlps;omega
  obtain ⟨rs,u,hu⟩ := split_last qs (by omega)
  subst xs ps qs
  refine ⟨(rs++[u])++[!a],by simp,(height_one_parent_safe_twins rs u a b hh).1,?_⟩
  intro hr
  exact hn (return8_of_flipped_parent_return rs u a b hh hr)

/-- With safety completeness available only at strictly smaller widths,
every height-one word at this width already returns as a whole. -/
theorem height_one_return_of_shorter_completeness (xs : List Bool)
    (hh : SpanOne (tr xs))
    (hshort : ∀ ys : List Bool, ys.length<xs.length → CedarSafety.Safe ys → evolution 8 ys=ys) :
    evolution 8 xs=xs := by
  by_contra hn
  obtain ⟨ys,hlen,hs,hr⟩ := height_one_nonreturn_shorter xs hh hn
  exact hr (hshort ys (by omega) hs)

/-- A minimum-width Safe/nonreturn counterexample must have white-height
span greater than one. This does not show that such a counterexample exists. -/
theorem minimal_safe_counterexample_not_height_one (xs : List Bool)
    (hn : evolution 8 xs≠xs)
    (hshort : ∀ ys : List Bool, ys.length<xs.length → CedarSafety.Safe ys → evolution 8 ys=ys) :
    ¬ SpanOne (tr xs) := fun hh => hn (height_one_return_of_shorter_completeness xs hh hshort)

end HeightOneDescent
