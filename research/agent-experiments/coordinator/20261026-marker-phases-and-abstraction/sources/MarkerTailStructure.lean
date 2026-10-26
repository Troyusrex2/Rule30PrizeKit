import MarkerCarryReconstruction

/-! Equal two-row marker/carry views hide only an alternating suffix
phase, apart from the newest bit. These are all-width structural statements
about collisions of the view, not a safety or return-completeness theorem. -/
namespace MarkerTailStructure
open CedarSafetySoundness MarkerCarryAmbiguity MarkerCarryReconstruction

theorem disagree_complement : ∀ a b : Bool, a ≠ b → b = !a := by
  decide +kernel

theorem complementary_or_alternates : ∀ a b c d : Bool,
    a ≠ b → c ≠ d → (c || a) = (d || b) → c = !a := by
  decide +kernel

theorem disagreement_next (xs ys : List Bool) (hv : view xs = view ys)
    (i : Nat) (hi : i + 2 < xs.length)
    (hd : xs.getD i false ≠ ys.getD i false) :
    xs.getD (i + 1) false ≠ ys.getD (i + 1) false := by
  obtain ⟨h0,h1⟩ := view_or_rows xs ys hv
  intro hn
  exact hd (previous_eq xs ys (view_length xs ys hv) h0 h1 i hi hn)

/-- A disagreement cannot disappear before the penultimate coordinate. -/
theorem disagreement_suffix (xs ys : List Bool) (hv : view xs = view ys)
    (k : Nat) (hd : xs.getD k false ≠ ys.getD k false) :
    ∀ j, k ≤ j → j + 1 < xs.length → xs.getD j false ≠ ys.getD j false := by
  intro j
  induction j with
  | zero =>
      intro hk _
      have he : k = 0 := by omega
      subst k
      exact hd
  | succ j ih =>
      intro hk hj
      by_cases he : k = j + 1
      · subst k
        exact hd
      · have hjd := ih (by omega) (by omega)
        exact disagreement_next xs ys hv j (by omega) hjd

/-- Every internal pair in the hidden suffix alternates in both words. -/
theorem disagreement_tail_alternates (xs ys : List Bool)
    (hv : view xs = view ys) (k : Nat)
    (hd : xs.getD k false ≠ ys.getD k false)
    (j : Nat) (hkj : k ≤ j) (hj : j + 2 < xs.length) :
    xs.getD (j + 1) false = !(xs.getD j false) ∧
      ys.getD (j + 1) false = !(ys.getD j false) := by
  have hlen := view_length xs ys hv
  have h0 := (view_or_rows xs ys hv).1
  have ho := congrArg (fun zs : List Bool => zs.getD (j + 2) false) h0
  rw [or_at_pair xs false false j hj,
    or_at_pair ys false false j (by omega)] at ho
  have ha := disagreement_suffix xs ys hv k hd j hkj (by omega)
  have hc := disagreement_suffix xs ys hv k hd (j+1) (by omega) (by omega)
  exact ⟨complementary_or_alternates _ _ _ _ ha hc ho,
    complementary_or_alternates _ _ _ _ (Ne.symm ha) (Ne.symm hc) ho.symm⟩

/-- An observed collision's internal difference is a complementary,
alternating suffix. The newest coordinate is deliberately not classified. -/
theorem hidden_suffix_structure (xs ys : List Bool)
    (hv : view xs = view ys) (k : Nat)
    (hd : xs.getD k false ≠ ys.getD k false) :
    (∀ j, k ≤ j → j + 1 < xs.length →
      ys.getD j false = !(xs.getD j false)) ∧
    (∀ j, k ≤ j → j + 2 < xs.length →
      xs.getD (j + 1) false = !(xs.getD j false) ∧
      ys.getD (j + 1) false = !(ys.getD j false)) := by
  constructor
  · intro j hk hj
    exact disagree_complement _ _ (disagreement_suffix xs ys hv k hd j hk hj)
  · exact disagreement_tail_alternates xs ys hv k hd

end MarkerTailStructure
