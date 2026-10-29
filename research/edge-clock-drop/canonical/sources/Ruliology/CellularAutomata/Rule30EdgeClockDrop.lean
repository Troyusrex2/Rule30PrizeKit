module

public import Ruliology.CellularAutomata.Rule30FrozenRuler

/-!
# A period drop cannot follow an antiperiodic parent

This is a local, unbounded-time result for the triangular Rule 30 edge
recurrence. It does not prove period monotonicity when the two preceding
columns have the same least period. No finite search is a premise.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30EdgeClockDrop

def Periodic (x : Nat → Bool) (h : Nat) : Prop := ∀ t, x (t+h) = x t
def Antiperiodic (x : Nat → Bool) (h : Nat) : Prop := ∀ t, x (t+h) = !(x t)

private theorem hidden_flip (a b c d : Bool)
    (s : d = xor c (a || b)) (s' : d = xor c ((!a) || b)) : b = true := by
  revert s s'
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem alternating_xor_constant (v w : Nat → Bool)
    (hv : ∀ t, v (t+1) = !(v t)) (hw : ∀ t, w (t+1) = !(w t)) :
    ∀ t, xor (v t) (w t) = xor (v 0) (w 0) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [hv, hw]
      have key (a b : Bool) : xor (!a) (!b) = xor a b := by
        cases a <;> cases b <;> rfl
      rw [key, ih]

/-- If the older column repeats after h and the previous column is
complemented after h, the next column cannot repeat after h. The auxiliary
older input is arbitrary; even a white boundary is unnecessary here. -/
theorem no_drop_after_antiperiod (u v w r : Nat → Bool) (h : Nat)
    (hu : Periodic u h) (hv : Antiperiodic v h)
    (sv : ∀ t, v (t+1) = xor (v t) (u t || r t))
    (sw : ∀ t, w (t+1) = xor (w t) (v t || u t)) :
    ¬ Periodic w h := by
  intro hw
  have black : ∀ t, u t = true := by
    intro t
    have shifted := sw (t+h)
    rw [show t+h+1 = (t+1)+h by omega, hw (t+1), hw t, hv t, hu t] at shifted
    exact hidden_flip (v t) (u t) (w t) (w (t+1)) (sw t) shifted
  have av : ∀ t, v (t+1) = !(v t) := by
    intro t
    rw [sv, black]
    cases v t <;> rfl
  have aw : ∀ t, w (t+1) = !(w t) := by
    intro t
    rw [sw, black]
    cases v t <;> cases w t <;> rfl
  have eq := alternating_xor_constant v w av aw h
  have vh : v h = !(v 0) := by simpa using hv 0
  have wh : w h = w 0 := by simpa using hw 0
  rw [vh, wh] at eq
  have impossible (a b : Bool) : xor (!a) b ≠ xor a b := by
    cases a <;> cases b <;> decide
  exact impossible (v 0) (w 0) eq

/-- The triangular update written as a spacetime recurrence. -/
def Triangular (x : Nat → Nat → Bool) : Prop :=
  ∀ j t, x (j+2) (t+1) = xor (x (j+2) t) (x (j+1) t || x j t)

private theorem driver_false (a b : Bool) (eq : a = xor a b) : b = false := by
  revert eq
  cases a <;> cases b <;> decide

/-- A constant column forces every older column to be identically white.
Only the triangular recurrence and its special first-column case are used. -/
theorem constant_column_white_prefix (x : Nat → Nat → Bool)
    (hs : ∀ t, x 1 (t+1) = xor (x 1 t) (x 0 t)) (hx : Triangular x) (j : Nat) :
    (∀ t, x j t = x j 0) → ∀ i, i < j → ∀ t, x i t = false := by
  induction j with
  | zero => intro hc i hi; omega
  | succ j ih =>
      intro hc
      cases j with
      | zero =>
          intro i hi t
          have hi0 : i = 0 := by omega
          subst i
          have eq := hs t
          rw [hc (t+1), hc t] at eq
          exact driver_false _ _ eq
      | succ n =>
          have white : ∀ t, x (n+1) t = false := by
            intro t
            have eq := hx n t
            rw [hc (t+1), hc t] at eq
            have h0 := driver_false _ _ eq
            have gate (a b : Bool) (h : (a || b) = false) : a = false := by
              revert h
              cases a <;> cases b <;> decide
            exact gate _ _ h0
          have older := ih (fun t => (white t).trans (white 0).symm)
          intro i hi t
          by_cases he : i = n+1
          · subst i; exact white t
          · exact older i (by omega) t

/-- An application at every interior position of any triangular history. -/
theorem no_drop_at_step (x : Nat → Nat → Bool) (hx : Triangular x) (j h : Nat)
    (hp : Periodic (x (j+1)) h) (ha : Antiperiodic (x (j+2)) h) :
    ¬ Periodic (x (j+3)) h := by
  apply no_drop_after_antiperiod (x (j+1)) (x (j+2)) (x (j+3)) (x j) h hp ha
  · exact hx j
  · exact hx (j+1)

theorem iter_triangular (c : Nat → Bool) :
    Triangular (fun j t => Rule30FrozenRuler.iter t c j) := by
  intro j t
  rfl

/-- On the official edge map, a clock-one column has an entirely white
older prefix. In particular, a nonconstant column cannot be followed by
a constant one. -/
theorem edge_constant_column_white_prefix (c : Nat → Bool) (j : Nat)
    (hc : ∀ t, Rule30FrozenRuler.iter t c j = c j) :
    ∀ i, i < j → ∀ t, Rule30FrozenRuler.iter t c i = false := by
  apply constant_column_white_prefix (fun i t => Rule30FrozenRuler.iter t c i)
    (fun _ => rfl) (iter_triangular c) j
  exact hc

/-- On the official edge map, no period h of column j can be followed by
an antiperiod h at j+1 and then a period h at j+2. This includes the first
two nonconstant edge columns and arbitrary initial codes. -/
theorem edge_no_drop_after_antiperiod (c : Nat → Bool) (j h : Nat)
    (hp : Periodic (fun t => Rule30FrozenRuler.iter t c j) h)
    (ha : Antiperiodic (fun t => Rule30FrozenRuler.iter t c (j+1)) h) :
    ¬ Periodic (fun t => Rule30FrozenRuler.iter t c (j+2)) h := by
  cases j with
  | zero =>
      apply no_drop_after_antiperiod
        (fun t => Rule30FrozenRuler.iter t c 0)
        (fun t => Rule30FrozenRuler.iter t c 1)
        (fun t => Rule30FrozenRuler.iter t c 2)
        (fun _ => false) h hp ha
      · intro t
        change xor (Rule30FrozenRuler.iter t c 1) (Rule30FrozenRuler.iter t c 0) =
          xor (Rule30FrozenRuler.iter t c 1) (Rule30FrozenRuler.iter t c 0 || false)
        simp
      · intro t; rfl
  | succ j =>
      exact no_drop_at_step (fun j t => Rule30FrozenRuler.iter t c j)
        (iter_triangular c) j h hp ha

end Ruliology.CellularAutomata.Rule30EdgeClockDrop
