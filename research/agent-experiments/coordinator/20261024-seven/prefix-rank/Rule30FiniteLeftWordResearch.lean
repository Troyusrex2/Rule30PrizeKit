import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! Exact finite-word representation of the official white-wall left
subsystem. Two updates retain all newly created cells; no old-radius cut
is made. Prefix locality is uniform in the word length and time. -/

namespace Rule30FiniteLeftWordResearch
open Ruliology.CellularAutomata.Rule30ZeroBoundary

def row (w : List Bool) : Nat → Bool
  | 0 => false
  | d+1 => w.getD d false

def next (w : List Bool) : List Bool :=
  (List.range (w.length+2)).map fun i => zrow (row w) 2 (i+1)

def Canonical (w : List Bool) : Prop := w.headD false=true ∧ w.reverse.headD false=true

theorem getD_large (w : List Bool) (i : Nat) (hi : w.length≤i) : w.getD i false=false := by
  induction w generalizing i with
  | nil => rfl
  | cons a w ih =>
    cases i with
    | zero => simp at hi
    | succ i => exact ih i (by simp only [List.length_cons] at hi; omega)

theorem getD_append_prefix (w v : List Bool) (i : Nat) (hi : i<w.length) :
    (w++v).getD i false=w.getD i false := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simp only [List.length_cons] at hi; omega)

theorem getD_snoc (w : List Bool) (b : Bool) : (w++[b]).getD w.length false=b := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ih

theorem mapRange_getD (f : Nat → Bool) (n i : Nat) (hi : i<n) :
    ((List.range n).map f).getD i false=f i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ,List.map_append]
    by_cases hin : i<n
    · rw [getD_append_prefix _ _ i (by simp; omega)]
      exact ih i hin
    · have he : i=n := by omega
      subst i
      have h:=getD_snoc ((List.range n).map f) (f n)
      simpa using h

theorem row_support (w : List Bool) (d : Nat) (hd : w.length<d) : row w d=false := by
  cases d with
  | zero => omega
  | succ i => exact getD_large w i (by omega)

theorem zrow_support {L : Nat → Bool} (W : Nat) (hL : ∀ d,W<d → L d=false) :
    ∀ t d,W+t<d → zrow L t d=false := by
  intro t
  induction t with
  | zero =>
    intro d hd
    rw [zrow_zero_of_pos L (show 1≤d by omega)]
    exact hL d (by omega)
  | succ t ih =>
    intro d hd
    cases d with
    | zero => omega
    | succ k =>
      rw [zrow_succ,ih (k+2) (by omega),ih (k+1) (by omega),ih k (by omega)]
      rfl

theorem length_next (w : List Bool) : (next w).length=w.length+2 := by simp [next]

theorem row_next (w : List Bool) : row (next w)=zrow (row w) 2 := by
  funext d
  cases d with
  | zero => exact (zrow_wall (row w) 2).symm
  | succ i =>
    by_cases hi : i<w.length+2
    · exact mapRange_getD (fun j=>zrow (row w) 2 (j+1)) (w.length+2) i hi
    · have hleft : row (next w) (i+1)=false := row_support (next w) (i+1) (by rw [length_next];omega)
      have hright := zrow_support w.length (row_support w) 2 (i+1) (by omega)
      rw [hleft,hright]

theorem zrow_prefix {L M : Nat → Bool} (W : Nat)
    (h : ∀ d,d≤W → L d=M d) :
    ∀ t d,t+d≤W → zrow L t d=zrow M t d := by
  intro t
  induction t with
  | zero =>
    intro d hd
    cases d with
    | zero => rw [zrow_wall,zrow_wall]
    | succ k => rw [zrow_zero,zrow_zero];exact h (k+1) (by omega)
  | succ t ih =>
    intro d hd
    cases d with
    | zero => rw [zrow_wall,zrow_wall]
    | succ k =>
      rw [zrow_succ,zrow_succ,ih (k+2) (by omega),ih (k+1) (by omega),ih k (by omega)]

end Rule30FiniteLeftWordResearch
