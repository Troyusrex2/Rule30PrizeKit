module
public import Rule30CommonPastResearch

/-! A finite WHITE-boundary diagnostic. Actual and Mode hold for all time.
Common holds at times 0,1,2 but fails at time 3. Initial subset is lost at
time 1. This refutes a short-window replacement for all-time Common, not
the all-time preservation conjecture. The finite witness was found by the
Cedar team and independently recovered and audited by the root agent. -/
@[expose] public section
namespace Rule30FiniteCommonWindowResearch
open Rule30CommonPastResearch
set_option maxHeartbeats 4000000

def row (w j : Nat) : Bool := if j<12 then w.testBit j else false

theorem row_zero (w j : Nat) (hj : 12≤j) : row w j=false := by
  simp only [row,if_neg (Nat.not_lt.mpr hj)]

theorem march_zero (w j : Nat) (hj : 14≤j) : march (row w) j=false := by
  cases j with
  | zero => omega
  | succ j =>
    cases j with
    | zero => omega
    | succ j =>
      simp only [march]
      rw [row_zero w (j+2) (by omega),row_zero w (j+1) (by omega),
        row_zero w j (by omega)]
      rfl

theorem mode_zero (a b h j : Nat) (hj : 14≤j) :
    modeStep (row a) (row b) (row h) j=false := by
  cases j with
  | zero => omega
  | succ j =>
    cases j with
    | zero => omega
    | succ j =>
      simp only [modeStep]
      rw [row_zero h (j+2) (by omega),row_zero h (j+1) (by omega),
        row_zero h j (by omega)]
      simp

def wa : Nat → Nat | 0 => 25 | 1 => 111 | 2 => 401 | 3 => 1783 | _ => 0
def wb : Nat → Nat | 0 => 2 | 1 => 14 | 2 => 50 | 3 => 222 | _ => 0
def wh : Nat → Nat | 0 => 24 | 1 => 104 | 2 => 392 | 3 => 1688 | _ => 0

theorem finite_steps : ∀ (t : Fin 3) (j : Fin 14),
    row (wa (t.val+1)) j.val=march (row (wa t.val)) j.val ∧
    row (wb (t.val+1)) j.val=march (row (wb t.val)) j.val ∧
    row (wh (t.val+1)) j.val=modeStep (row (wa t.val)) (row (wb t.val))
      (row (wh t.val)) j.val := by decide +kernel

theorem whole_steps (t : Fin 3) (j : Nat) :
    row (wa (t.val+1)) j=march (row (wa t.val)) j ∧
    row (wb (t.val+1)) j=march (row (wb t.val)) j ∧
    row (wh (t.val+1)) j=modeStep (row (wa t.val)) (row (wb t.val))
      (row (wh t.val)) j := by
  by_cases hj : j<14
  · exact finite_steps t ⟨j,hj⟩
  · have hi : 14≤j := by omega
    rw [row_zero _ j (by omega),row_zero _ j (by omega),row_zero _ j (by omega),
      march_zero _ j hi,march_zero _ j hi,mode_zero _ _ _ j hi]
    exact ⟨rfl,rfl,rfl⟩

def actual (w : Nat) : Nat → Nat → Bool
  | 0 => row w
  | t+1 => march (actual w t)
def A := actual 25
def B := actual 2
def H : Nat → Nat → Bool
  | 0 => row 24
  | t+1 => modeStep (A t) (B t) (H t)

theorem actual_a : Actual A := fun _ _ => rfl
theorem actual_b : Actual B := fun _ _ => rfl
theorem mode_h : Mode A B H := fun _ _ => rfl

theorem rows_match : ∀ t, t≤3 →
    A t=row (wa t) ∧ B t=row (wb t) ∧ H t=row (wh t) := by
  intro t
  induction t with
  | zero => intro _;exact ⟨rfl,rfl,rfl⟩
  | succ t ih =>
    intro ht
    obtain ⟨ha,hb,hh⟩ := ih (by omega)
    refine ⟨?_,?_,?_⟩
    · funext j
      change march (A t) j=row (wa (t+1)) j
      rw [ha]
      exact (whole_steps ⟨t,by omega⟩ j).1.symm
    · funext j
      change march (B t) j=row (wb (t+1)) j
      rw [hb]
      exact (whole_steps ⟨t,by omega⟩ j).2.1.symm
    · funext j
      change modeStep (A t) (B t) (H t) j=row (wh (t+1)) j
      rw [ha,hb,hh]
      exact (whole_steps ⟨t,by omega⟩ j).2.2.symm

theorem finite_common : ∀ (t : Fin 3) (j : Fin 12),
    (xor (row (wa t.val) j.val) (row (wb t.val) j.val) && row (wh t.val) (j.val+1)) =
    (row (wh t.val) j.val && xor (row (wa t.val) (j.val+1)) (row (wb t.val) (j.val+1))) :=
  by decide +kernel

theorem common_window (t : Nat) (ht : t≤2) : ∀ j, GoodAt A B H t j := by
  intro j
  obtain ⟨ha,hb,hh⟩ := rows_match t (by omega)
  unfold GoodAt
  rw [ha,hb,hh]
  by_cases hj : j<12
  · exact finite_common ⟨t,by omega⟩ ⟨j,hj⟩
  · rw [row_zero _ j (by omega),row_zero _ j (by omega),row_zero _ j (by omega)]
    rfl

theorem initially_subset : ∀ j, SubAt A B H 0 j := by
  intro j
  change (row 24 j && xor (row 25 j) (row 2 j))=row 24 j
  by_cases hj : j<12
  · have finite_check : ∀ i : Fin 12,
        (row 24 i.val && xor (row 25 i.val) (row 2 i.val))=row 24 i.val := by decide +kernel
    exact finite_check ⟨j,hj⟩
  · rw [row_zero 24 j (by omega)]
    rfl

theorem subset_fails_at_one : ¬SubAt A B H 1 3 := by decide +kernel
theorem common_fails_at_three : ¬GoodAt A B H 3 3 := by decide +kernel
theorem finite_initial : Finite (A 0) ∧ Finite (B 0) ∧ Finite (H 0) :=
  ⟨⟨12,fun j hj => row_zero 25 j hj⟩,
   ⟨12,fun j hj => row_zero 2 j hj⟩,
   ⟨12,fun j hj => row_zero 24 j hj⟩⟩

/-- Genuine white-boundary dynamics from finite initial rows, but only a
three-row Common window. The all-time Common premise is explicitly false. -/
theorem finite_common_window_does_not_preserve_subset :
    Actual A ∧ Actual B ∧ Mode A B H ∧
    Finite (A 0) ∧ Finite (B 0) ∧ Finite (H 0) ∧
    (∀ t, t≤2 → ∀ j, GoodAt A B H t j) ∧
    (∀ j, SubAt A B H 0 j) ∧ ¬SubAt A B H 1 3 ∧ ¬GoodAt A B H 3 3 :=
  ⟨actual_a,actual_b,mode_h,finite_initial.1,finite_initial.2.1,finite_initial.2.2,
    common_window,initially_subset,subset_fails_at_one,common_fails_at_three⟩

end Rule30FiniteCommonWindowResearch
