import HeightOneSemantics

/-! A genuine finite-white height-one column that is not four-periodic
produces a strictly shorter Safe word that fails whole-word return8.
No global safety completeness or unconditional twin rigidity is assumed. -/
namespace HeightOneTransfer
open CedarSafetySoundness CedarSafety HeightOneLogic HeightOneSemantics
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem genuine_no11011 (xs : List Bool) : HeightOneLogic.No11011 (tr xs) := by
  intro t h
  apply CedarNo11011.finite_white_no11011 xs t
  simpa only [trace_eq] using h

theorem four_of_derivative_two (b : Nat → Bool)
    (h : ∀ t, D b (t+2)=D b t) : Periodic b 4 := by
  have cancel4 : ∀ a b c d e : Bool,
      xor c d=xor a b → xor d e=xor b c → e=a := by decide +kernel
  intro t
  have h0 := h t
  have h1 := h (t+1)
  unfold D at h0 h1
  simp only [Nat.add_assoc] at h0 h1
  exact cancel4 _ _ _ _ _ h0 h1

theorem transfer_three (xs : List Bool) (u a b : Bool)
    (P : Nat) (hP : 0<P)
    (hp : Periodic (tr (((xs++[u])++[a])++[b])) P)
    (hh : SpanOne (tr (((xs++[u])++[a])++[b])))
    (hn : ¬ Periodic (tr (((xs++[u])++[a])++[b])) 4) :
    CedarSafety.Safe ((xs++[u])++[!a]) ∧
      evolution 8 ((xs++[u])++[!a]) ≠ (xs++[u])++[!a] := by
  let B := tr (((xs++[u])++[a])++[b])
  let A := tr ((xs++[u])++[a])
  let U := tr (xs++[u])
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
  constructor
  · intro t bad
    have localFact : ∀ x : Bool, (!x)=false → x=true := by decide +kernel
    have h0 : (Bool.not (A t))=false := by
      simpa only [← trace_eq,leaf_flip_trace] using bad.1
    have h1 : (Bool.not (A (t+1)))=false := by
      simpa only [← trace_eq,leaf_flip_trace] using bad.2
    apply hi t
    rw [← hA t,← hA (t+1)]
    exact ⟨localFact _ h0,localFact _ h1⟩
  · intro hr
    have hrA : evolution 8 ((xs++[u])++[a])=(xs++[u])++[a] :=
      (leaf_flip_return (xs++[u]) a 8).mp hr
    have twins (t : Nat) : A t=U t := (hA t).trans (hU t).symm
    have htwo := return8_twins_two (xs++[u]) a hrA twins
    apply hn
    apply four_of_derivative_two
    intro t
    rw [← hA (t+2),← hA t]
    exact htwo t

theorem small_return4 (xs : List Bool) (hl : xs.length≤2) : evolution 4 xs=xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
      cases xs with
      | nil => cases a <;> decide +kernel
      | cons b xs =>
          cases xs with
          | nil => cases a <;> cases b <;> decide +kernel
          | cons c xs => simp at hl

theorem trace_period_of_return (xs : List Bool) (P : Nat) (hr : evolution P xs=xs) :
    Periodic (tr xs) P := by
  intro t
  rw [trace_eq,evolution_add,hr,trace_eq]

theorem split_last (xs : List Bool) (h : 0<xs.length) : ∃ ys v, xs=ys++[v] := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      cases xs with
      | nil => exact ⟨[],x,rfl⟩
      | cons y ys =>
          obtain ⟨ps,v,hv⟩ := ih (by simp)
          exact ⟨x::ps,v,by rw [hv];rfl⟩

/-- The explicit even column period and closed finite height window are
lifted to all time before any trace argument. The shorter word is genuine. -/
theorem height_one_shorter_counterexample (xs : List Bool)
    (P : Nat) (hP : 0<P) (he : Even P) (hp : Periodic (tr xs) P)
    (hc : WH (tr xs) P=0)
    (hh : ∃ lo : Int, ∀ t, t≤P → lo≤WH (tr xs) t ∧ WH (tr xs) t≤lo+1)
    (hn : ¬ Periodic (tr xs) 4) :
    ∃ ys : List Bool, ys.length+1=xs.length ∧ CedarSafety.Safe ys ∧ evolution 8 ys≠ys := by
  have hs := span_one_of_closed_period (tr xs) P hP he hp hc hh
  have hlen : 3≤xs.length := by
    by_contra h
    exact hn (trace_period_of_return xs 4 (small_return4 xs (by omega)))
  obtain ⟨ps,b,hb⟩ := split_last xs (by omega)
  have hlps : 2≤ps.length := by rw [hb,List.length_append] at hlen;simp at hlen;omega
  obtain ⟨qs,a,ha⟩ := split_last ps (by omega)
  have hlqs : 1≤qs.length := by rw [ha,List.length_append] at hlps;simp at hlps;omega
  obtain ⟨rs,u,hu⟩ := split_last qs (by omega)
  subst xs ps qs
  obtain ⟨hsafe,hret⟩ := transfer_three rs u a b P hP hp hs hn
  refine ⟨(rs++[u])++[!a],?_,hsafe,hret⟩
  simp

/-- A minimal-width Safe counterexample cannot be preceded at its own width
by a height-one non-four-periodic column. No converse descent is asserted. -/
theorem height_one_four_of_shorter_completeness (xs : List Bool)
    (P : Nat) (hP : 0<P) (he : Even P) (hp : Periodic (tr xs) P)
    (hc : WH (tr xs) P=0)
    (hh : ∃ lo : Int, ∀ t, t≤P → lo≤WH (tr xs) t ∧ WH (tr xs) t≤lo+1)
    (hshort : ∀ ys : List Bool, ys.length<xs.length → CedarSafety.Safe ys → evolution 8 ys=ys) :
    Periodic (tr xs) 4 := by
  by_contra hn
  obtain ⟨ys,hlen,hs,hr⟩ := height_one_shorter_counterexample xs P hP he hp hc hh hn
  exact hr (hshort ys (by omega) hs)

end HeightOneTransfer
