import MarkerCarryAmbiguity

/-! Two marker rows and two full carry rows, together with the final two
initial bits, reconstruct the entire finite word. The quotient hides at
most these two Boolean choices; restoring them is essentially full-state
retention, not a new safety or marker-propagation invariant. -/
namespace MarkerCarryReconstruction
open CedarSafetySoundness CedarMarkerReturnTwo MarkerCarryAmbiguity
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def orRow (p r : Bool) : List Bool → List Bool
  | [] => []
  | v::vs => (p || r) :: orRow v p vs

theorem or_from_carry_marker (xs : List Bool) (p r s : Bool) :
    orRow p r xs=List.zipWith xor (carries p r s xs) (marks p r s xs) := by
  have localFact : ∀ p r s : Bool, xor (carry p r s) (marker p r s)=(p || r) := by decide +kernel
  induction xs generalizing p r s with
  | nil => rfl
  | cons v vs ih =>
      simp only [orRow,carries,marks,List.zipWith_cons_cons,localFact]
      rw [ih v p r]

theorem view_or_rows (xs ys : List Bool) (h : view xs=view ys) :
    orRow false false xs=orRow false false ys ∧
      orRow false false (F xs)=orRow false false (F ys) := by
  have m0 := congrArg View.markers0 h
  have m1 := congrArg View.markers1 h
  have c0 := congrArg View.carries0 h
  have c1 := congrArg View.carries1 h
  change marked xs=marked ys at m0
  change marked (F xs)=marked (F ys) at m1
  change fullCarry xs=fullCarry ys at c0
  change fullCarry (F xs)=fullCarry (F ys) at c1
  constructor
  · rw [or_from_carry_marker xs false false false,or_from_carry_marker ys false false false]
    change List.zipWith xor (fullCarry xs) (marked xs)=List.zipWith xor (fullCarry ys) (marked ys)
    rw [m0,c0]
  · rw [or_from_carry_marker (F xs) false false false,or_from_carry_marker (F ys) false false false]
    change List.zipWith xor (fullCarry (F xs)) (marked (F xs))=
      List.zipWith xor (fullCarry (F ys)) (marked (F ys))
    rw [m1,c1]

theorem change_length (xs : List Bool) (p r : Bool) : (change p r xs).length=xs.length := by
  induction xs generalizing p r with
  | nil => rfl
  | cons v vs ih => simp only [change,List.length_cons,ih]

theorem marks_length (xs : List Bool) (p r s : Bool) : (marks p r s xs).length=xs.length := by
  induction xs generalizing p r s with
  | nil => rfl
  | cons v vs ih => simp only [marks,List.length_cons,ih]

theorem view_length (xs ys : List Bool) (h : view xs=view ys) : xs.length=ys.length := by
  have hm := congrArg (fun v : View => v.markers0.length) h
  simpa only [view,marked,marks_length] using hm

theorem change_at (xs : List Bool) (p r : Bool) (i : Nat) :
    (change p r xs).getD i false=xor (xs.getD i false) ((orRow p r xs).getD i false) := by
  induction xs generalizing p r i with
  | nil => cases i <;> rfl
  | cons v vs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih v p i

theorem or_at_pair (xs : List Bool) (p r : Bool) (i : Nat) (hi : i+2<xs.length) :
    (orRow p r xs).getD (i+2) false=(xs.getD (i+1) false || xs.getD i false) := by
  induction xs generalizing p r i with
  | nil => simp at hi
  | cons v vs ih =>
      cases i with
      | zero =>
          cases vs with
          | nil => simp at hi
          | cons w ws =>
              cases ws with
              | nil => simp at hi
              | cons a as => rfl
      | succ i => exact ih v p i (by simp only [List.length_cons] at hi;omega)

theorem or_covers (xs : List Bool) (p r : Bool) (i : Nat) (hi : i+1<xs.length)
    (hb : xs.getD i false=true) : (orRow p r xs).getD (i+1) false=true := by
  induction xs generalizing p r i with
  | nil => simp at hi
  | cons v vs ih =>
      cases i with
      | zero =>
          cases vs with
          | nil => simp at hi
          | cons w ws =>
              change (v || p)=true
              change v=true at hb
              rw [hb]
              rfl
      | succ i => exact ih v p i (by simp only [List.length_cons] at hi;omega) hb

theorem local_no_recoalescence : ∀ a b c d z f : Bool,
    (a=true → f=true) → (b=true → f=true) →
    (c || a)=(d || b) →
    (xor c f || xor a z)=(xor d f || xor b z) →
    c=d → a=b := by decide +kernel

theorem previous_eq (xs ys : List Bool) (hlen : xs.length=ys.length)
    (h0 : orRow false false xs=orRow false false ys)
    (h1 : orRow false false (F xs)=orRow false false (F ys))
    (i : Nat) (hi : i+2<xs.length)
    (hn : xs.getD (i+1) false=ys.getD (i+1) false) :
    xs.getD i false=ys.getD i false := by
  have hA (j : Nat) := congrArg (fun zs : List Bool => zs.getD j false) h0
  have hcur := hA (i+2)
  rw [or_at_pair xs false false i hi,
    or_at_pair ys false false i (by omega)] at hcur
  have hnew := congrArg (fun zs : List Bool => zs.getD (i+2) false) h1
  rw [or_at_pair (F xs) false false i (by simpa only [F,change_length] using hi),
    or_at_pair (F ys) false false i (by simp only [F,change_length];omega)] at hnew
  simp only [F,change_at] at hnew
  rw [← hA i,← hA (i+1)] at hnew
  apply local_no_recoalescence _ _ _ _ _ _ ?_ ?_ hcur hnew hn
  · exact or_covers xs false false i (by omega)
  · intro hy
    rw [hA (i+1)]
    exact or_covers ys false false i (by omega) hy

theorem list_ext_getD (xs ys : List Bool) (hlen : xs.length=ys.length)
    (h : ∀ i, i<xs.length → xs.getD i false=ys.getD i false) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons v vs ih =>
      cases ys with
      | nil => simp at hlen
      | cons w ws =>
          have hv : v=w := h 0 (by simp)
          have ht : vs=ws := ih ws (by simpa using hlen)
            (fun i hi => h (i+1) (by simpa using hi))
          rw [hv,ht]

/-- With the final two initial bits retained, this view is injective at
ALL finite widths, including the empty and one-bit cases. -/
theorem view_and_last_two_injective (xs ys : List Bool) (hv : view xs=view ys)
    (hlast : xs.getD (xs.length-1) false=ys.getD (ys.length-1) false)
    (hpenult : xs.getD (xs.length-2) false=ys.getD (ys.length-2) false) : xs=ys := by
  have hlen := view_length xs ys hv
  obtain ⟨h0,h1⟩ := view_or_rows xs ys hv
  have recover : ∀ k : Nat, k+1<xs.length → xs.getD k false=ys.getD k false →
      ∀ i, i≤k → xs.getD i false=ys.getD i false := by
    intro k
    induction k with
    | zero =>
        intro _ hk i hi
        have he : i=0 := by omega
        subst i
        exact hk
    | succ k ih =>
        intro hb hk i hi
        have hp := previous_eq xs ys hlen h0 h1 k (by omega) hk
        by_cases he : i=k+1
        · subst i;exact hk
        · exact ih (by omega) hp i (by omega)
  apply list_ext_getD xs ys hlen
  intro i hi
  by_cases he : i=xs.length-1
  · subst i
    simpa only [← hlen] using hlast
  · have hn : 2≤xs.length := by omega
    have hp : xs.getD (xs.length-2) false=ys.getD (xs.length-2) false := by
      simpa only [← hlen] using hpenult
    exact recover (xs.length-2) (by omega) hp i (by omega)

end MarkerCarryReconstruction
