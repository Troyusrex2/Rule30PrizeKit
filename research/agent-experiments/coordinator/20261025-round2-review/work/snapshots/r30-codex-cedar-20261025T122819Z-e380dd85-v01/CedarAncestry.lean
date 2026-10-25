module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Realization

/-!
Round two, R2-04. Noncrossing disagreement ancestry after local cancellation.
This does NOT prove that a source reaches the center. Rule 210 below has the
same local selection property and an eventually white single-seed center.
-/

@[expose] public section
namespace CedarAncestry
open Ruliology.CellularAutomata

def out (g : Bool → Bool → Bool) (al ac ar bl bc br : Bool) : Bool :=
  xor (xor al (g ac ar)) (xor bl (g bc br))

def idx (dl dc : Bool) : Nat := if dl then 0 else if dc then 1 else 2

def derivativeC (g : Bool → Bool → Bool) (r : Bool) : Bool :=
  xor (g false r) (g true r)

def derivativeR (g : Bool → Bool → Bool) (c : Bool) : Bool :=
  xor (g c false) (g c true)

def switch (g : Bool → Bool → Bool) (dl dc dr ar : Bool) : Bool :=
  !dl && dc && dr && !(derivativeC g ar)

def weights (g : Bool → Bool → Bool) (al ac ar bl bc br : Bool) : Bool × Bool × Bool :=
  let dl := xor al bl
  let dc := xor ac bc
  let dr := xor ar br
  let sw := switch g dl dc dr ar
  (dl, (if sw then derivativeC g br else derivativeC g ar) && dc,
       (if sw then derivativeR g ac else derivativeR g bc) && dr)

def parity (w : Bool × Bool × Bool) : Bool := xor w.1 (xor w.2.1 w.2.2)
def selected (w : Bool × Bool × Bool) (i : Nat) : Bool :=
  if i = 0 then w.1 else if i = 1 then w.2.1 else w.2.2
def remainder (w : Bool × Bool × Bool) (i : Nat) : Bool :=
  if i = 0 then xor w.2.1 w.2.2
  else if i = 1 then xor w.1 w.2.2 else xor w.1 w.2.1

/-- Exact local pairing certificate: at an output disagreement, preserve the
leftmost differing parent, and the other active contributions have even parity.
With at most two others, they are absent or paired. -/
def Normalizes (g : Bool → Bool → Bool) : Prop :=
  ∀ al ac ar bl bc br,
    let w := weights g al ac ar bl bc br
    let i := idx (xor al bl) (xor ac bc)
    parity w = out g al ac ar bl bc br ∧
    (out g al ac ar bl bc br = true → selected w i = true ∧ remainder w i = false)

theorem rule30_normalizes : Normalizes (· || ·) := by
  intro al ac ar bl bc br
  cases al <;> cases ac <;> cases ar <;> cases bl <;> cases bc <;> cases br <;> decide

theorem rule210_normalizes : Normalizes (fun c r => !c && r) := by
  intro al ac ar bl bc br
  cases al <;> cases ac <;> cases ar <;> cases bl <;> cases bc <;> cases br <;> decide

def parent (d : Int → Bool) (x : Int) : Int :=
  if d (x-1) then x-1 else if d x then x else x+1

theorem parent_bounds (d : Int → Bool) (x : Int) :
    x-1 ≤ parent d x ∧ parent d x ≤ x+1 := by
  unfold parent
  split <;> try omega

theorem parent_neighbor (d : Int → Bool) (x : Int) :
    parent d x ≤ parent d (x+1) := by
  have hx : x+1-1 = x := by omega
  cases h0 : d (x-1) <;> cases h1 : d x <;> cases h2 : d (x+1) <;>
    simp [parent, hx, h0, h1, h2] <;> omega

/-- Parent edges never cross (for any discrepancy mask). -/
theorem parent_monotone (d : Int → Bool) (x y : Int) (h : x ≤ y) :
    parent d x ≤ parent d y := by
  by_cases h0 : y = x
  · subst y; exact Int.le_refl _
  by_cases h1 : y = x+1
  · subst y; exact parent_neighbor d x
  have hx := parent_bounds d x
  have hy := parent_bounds d y
  omega

def ancestor (d : Nat → Int → Bool) : Nat → Int → Int
  | 0, x => x
  | t+1, x => ancestor d t (parent (d t) x)

/-- Ordered root labels at every finite time, without a fixed window bound. -/
theorem ancestor_monotone (d : Nat → Int → Bool) (t : Nat) :
    ∀ x y, x ≤ y → ancestor d t x ≤ ancestor d t y := by
  induction t with
  | zero => intro x y h; exact h
  | succ t ih =>
    intro x y h
    exact ih _ _ (parent_monotone (d t) x y h)

/-- Any locally valid parent rule gives a real initial disagreement ancestor. -/
theorem ancestor_valid (d : Nat → Int → Bool)
    (hstep : ∀ t x, d (t+1) x = true → d t (parent (d t) x) = true)
    (t : Nat) : ∀ x, d t x = true → d 0 (ancestor d t x) = true := by
  induction t with
  | zero => intro x h; exact h
  | succ t ih => intro x h; exact ih _ (hstep t x h)

def diff (a b : Int → Bool) (x : Int) : Bool := xor (a x) (b x)

theorem parent_valid30 (a b : Int → Bool) (x : Int)
    (h : out (· || ·) (a (x-1)) (a x) (a (x+1))
      (b (x-1)) (b x) (b (x+1)) = true) :
    diff a b (parent (diff a b) x) = true := by
  cases ha : a (x-1) <;> cases hb : a x <;> cases hc : a (x+1) <;>
    cases hd : b (x-1) <;> cases he : b x <;> cases hf : b (x+1) <;>
    simp_all [parent, diff, out]

theorem parent_valid210 (a b : Int → Bool) (x : Int)
    (h : out (fun c r => !c && r) (a (x-1)) (a x) (a (x+1))
      (b (x-1)) (b x) (b (x+1)) = true) :
    diff a b (parent (diff a b) x) = true := by
  cases ha : a (x-1) <;> cases hb : a x <;> cases hc : a (x+1) <;>
    cases hd : b (x-1) <;> cases he : b x <;> cases hf : b (x+1) <;>
    simp_all [parent, diff, out]

def Evolves (g : Bool → Bool → Bool) (a : Nat → Int → Bool) : Prop :=
  ∀ t x, a (t+1) x = xor (a t (x-1)) (g (a t x) (a t (x+1)))

/-- Every surviving disagreement in two Rule 30 histories has the selected
initial ancestor. This does not assert any survivor at a chosen target. -/
theorem rule30_ancestry (a b : Nat → Int → Bool)
    (ha : Evolves (· || ·) a) (hb : Evolves (· || ·) b) (t : Nat) (x : Int)
    (h : diff (a t) (b t) x = true) :
    diff (a 0) (b 0) (ancestor (fun s => diff (a s) (b s)) t x) = true := by
  apply ancestor_valid (fun s => diff (a s) (b s)) ?_ t x h
  intro s y hh
  apply parent_valid30 (a s) (b s) y
  simpa [diff, out, ha s y, hb s y] using hh

/-- Bridge to the exact official single-seed evolution, at any time shift. -/
theorem seed_shift_evolves (T : Nat) :
    Evolves (· || ·) (fun t x => Rule30Jen.cell (T+t) x) := by
  intro t x
  change Rule30Jen.cell (T+t+1) x = _
  rfl

def canonicalDiff (T P t : Nat) : Int → Bool :=
  diff (Rule30Jen.cell (T+t)) (Rule30Jen.cell (T+P+t))

/-- Specialization to official seed comparisons; still conditional on a
disagreement, and still no assertion of a disagreement at the center. -/
theorem canonical_ancestry (T P t : Nat) (x : Int)
    (h : canonicalDiff T P t x = true) :
    canonicalDiff T P 0 (ancestor (canonicalDiff T P) t x) = true := by
  exact rule30_ancestry (fun s x => Rule30Jen.cell (T+s) x)
    (fun s x => Rule30Jen.cell (T+P+s) x)
    (seed_shift_evolves T) (seed_shift_evolves (T+P)) t x h

theorem rule210_ancestry (a b : Nat → Int → Bool)
    (ha : Evolves (fun c r => !c && r) a)
    (hb : Evolves (fun c r => !c && r) b) (t : Nat) (x : Int)
    (h : diff (a t) (b t) x = true) :
    diff (a 0) (b 0) (ancestor (fun s => diff (a s) (b s)) t x) = true := by
  apply ancestor_valid (fun s => diff (a s) (b s)) ?_ t x h
  intro s y hh
  apply parent_valid210 (a s) (b s) y
  simpa [diff, out, ha s y, hb s y] using hh

/-- The nonlinear Rule 210 shares the new ancestry property but its actual
single-seed comparison T=P=1 has no center discrepancy, at any future time.
The center theorem is an existing pinned catalog result, not a new discovery. -/
theorem rule210_coupled_center_agrees (t : Nat) :
    Rule30Realization.run Rule30Realization.g210 (t+1) 0 =
    Rule30Realization.run Rule30Realization.g210 (t+2) 0 := by
  rw [Rule30Realization.center210 t, Rule30Realization.center210 (t+1)]

end CedarAncestry
