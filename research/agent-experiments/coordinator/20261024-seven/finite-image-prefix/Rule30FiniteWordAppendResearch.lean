import Rule30FiniteLeftWordResearch

namespace Rule30FiniteWordAppendResearch
open Rule30FiniteLeftWordResearch (row getD_append_prefix)

theorem getD_append_right (w v : List Bool) (i : Nat) (hi : w.length≤i) :
    (w++v).getD i false=v.getD (i-w.length) false := by
  induction w generalizing i with
  | nil => rfl
  | cons a w ih =>
    cases i with
    | zero => simp only [List.length_cons] at hi;omega
    | succ i =>
      rw [List.cons_append,List.getD_cons_succ,List.length_cons,
        show i+1-(w.length+1)=i-w.length by omega]
      exact ih i (by simp only [List.length_cons] at hi;omega)

theorem getD_replicate (b : Bool) (n i : Nat) :
    (List.replicate n b).getD i false=if i<n then b else false := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_replicate]
  by_cases h : i<n <;> simp [h]

theorem row_append_prefix (u v : List Bool) (d : Nat) (hd : d≤u.length) :
    row (u++v) d=row u d := by
  cases d with
  | zero => rfl
  | succ d => exact getD_append_prefix u v d (by omega)

theorem row_middle (u v : List Bool) (b : Bool) (n d : Nat)
    (h0 : u.length<d) (h1 : d≤u.length+n) :
    row (u++List.replicate n b++v) d=b := by
  cases d with
  | zero => omega
  | succ d =>
    change ((u++List.replicate n b)++v).getD d false=b
    rw [getD_append_prefix _ _ d (by simp;omega),getD_append_right u _ d (by omega),
      getD_replicate]
    rw [ite_eq_left (by omega)]

theorem row_tail_shift (u v : List Bool) (b : Bool) (n d : Nat)
    (hd : u.length+n<d) :
    row (u++List.replicate n b++v) d=row (u++v) (d-n) := by
  obtain ⟨i,hi⟩ : ∃ i,d=i+1 := ⟨d-1,by omega⟩
  subst d
  obtain ⟨j,hj⟩ : ∃ j,i+1-n=j+1 := ⟨i-n,by omega⟩
  change ((u++List.replicate n b)++v).getD i false=row (u++v) (i+1-n)
  rw [hj]
  change ((u++List.replicate n b)++v).getD i false=(u++v).getD j false
  rw [getD_append_right _ _ i (by simp;omega),getD_append_right _ _ j (by omega)]
  simp only [List.length_append,List.length_replicate]
  congr 1
  omega

end Rule30FiniteWordAppendResearch
