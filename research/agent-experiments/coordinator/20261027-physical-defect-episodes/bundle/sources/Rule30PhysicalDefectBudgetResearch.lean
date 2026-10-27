module
public import Ruliology.CellularAutomata.Rule30MaskedJen

/-! Physical masked time-shift defects for the actual single-seed Rule 30 pattern.
The lower bound follows from the official doubling-window theorem. The upper
budget in `problem1_of_fixed_budget` is an explicit unproved premise, with all
parameters fixed before the horizon is quantified. No moving-diagonal or
finite-list clock is substituted for physical columns 0, 1, and 2. -/
@[expose] public section
namespace Rule30PhysicalDefectBudgetResearch
open Ruliology.CellularAutomata Rule30Jen Rule30Prize

def maskedDefect (Q t : Nat) : Bool :=
  !(cell t 0) && xor (cell t 1) (cell (t-Q) 1)

/-- The number of true values in the half-open interval `[lo,hi)`.
The count is zero when `hi ≤ lo`. -/
def intervalCount (p : Nat → Bool) (lo hi : Nat) : Nat :=
  (List.range' lo (hi-lo)).countP p

def defectCount (Q n0 X : Nat) : Nat := intervalCount (maskedDefect Q) n0 X

theorem intervalCount_split (p : Nat → Bool) {a b c : Nat}
    (hab : a≤b) (hbc : b≤c) :
    intervalCount p a c = intervalCount p a b + intervalCount p b c := by
  unfold intervalCount
  rw [show c-a=(b-a)+(c-b) by omega, ← List.range'_append_1, List.countP_append]
  rw [show a+(b-a)=b by omega]

theorem intervalCount_pos (p : Nat → Bool) {a b s : Nat}
    (has : a≤s) (hsb : s<b) (hp : p s=true) : 1≤intervalCount p a b := by
  apply List.one_le_countP_iff.mpr
  refine ⟨s, List.mem_range'.mpr ⟨s-a, by omega, ?_⟩, hp⟩
  omega

theorem periodic_multiple {T P Q : Nat}
    (hc : ∀ t, T≤t → cell (t+P) 0=cell t 0) (hPQ : P∣Q) :
    ∀ t, T≤t → cell (t+Q) 0=cell t 0 := by
  obtain ⟨k,rfl⟩ := hPQ
  induction k with
  | zero => simp
  | succ k ih =>
      intro t ht
      rw [Nat.mul_succ, ← Nat.add_assoc, hc _ (by omega), ih t ht]

theorem defect_window {T Q : Nat} (hQ : 0<Q)
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0)
    (n : Nat) (hn : T+Q≤n) : 1≤defectCount Q n (2*n) := by
  obtain ⟨s,hns,hsn,hw,hd⟩ := Rule30MaskedJen.periodic_window hQ hc n hn
  apply intervalCount_pos _ hns hsn
  unfold maskedDefect
  rw [hw]
  cases h1 : cell s 1 <;> cases h2 : cell (s-Q) 1 <;> simp_all

/-- One distinct masked defect per disjoint doubling window. -/
theorem doubling_lower {T Q n0 : Nat} (hQ : 0<Q)
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0) (hn0 : T+Q≤n0) (k : Nat) :
    k≤defectCount Q n0 (2^k*n0) := by
  induction k with
  | zero => simp [defectCount, intervalCount]
  | succ k ih =>
      have hp : n0≤2^k*n0 := by
        have hh := Nat.mul_le_mul_right n0 (Nat.one_le_pow k 2 (by decide))
        simpa using hh
      have hw := defect_window hQ hc (2^k*n0) (by omega)
      have he : 2^(k+1)*n0=2*(2^k*n0) := by
        simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
      rw [he]
      unfold defectCount at ih hw ⊢
      rw [intervalCount_split _ hp (by omega)]
      omega

/-- The exact base-four lower bound, including the empty interval at `m=0`. -/
theorem base_four_lower {T Q n0 : Nat} (hQ : 0<Q)
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0) (hn0 : T+Q≤n0) (m : Nat) :
    2*m≤defectCount Q n0 (4^m*n0) := by
  have h := doubling_lower hQ hc hn0 (2*m)
  simpa only [Nat.pow_mul, show (2:Nat)^2=4 by decide] using h

/-- A conditional interface to official Problem 1. The fixed upper budget is
the missing mathematical premise; this theorem does not establish that budget. -/
theorem problem1_of_fixed_budget
    (upper : ∀ T P : Nat, 0<P →
      (∀ t, T≤t → cell (t+P) 0=cell t 0) →
      ∃ Q n0 C M : Nat, 0<Q ∧ P∣Q ∧ T+Q≤n0 ∧
        ∀ m, M≤m → defectCount Q n0 (4^m*n0)≤C+m) : Problem1 := by
  rintro ⟨T,P,hP,hc⟩
  obtain ⟨Q,n0,C,M,hQ,hPQ,hn0,hu⟩ := upper T P hP hc
  have hq := periodic_multiple hc hPQ
  have lo := base_four_lower hQ hq hn0 (M+C+1)
  have hi := hu (M+C+1) (by omega)
  omega

def mismatch (Q t : Nat) : Bool := xor (cell t 1) (cell (t-Q) 1)
def persists (t : Nat) : Bool := !(cell t 2)
def forcing (Q t : Nat) : Bool :=
  !(cell (t-Q) 1) && xor (cell t 2) (cell (t-Q) 2)

theorem or_difference (r z ro zo : Bool) :
    xor (r || z) (ro || zo) =
      xor ((!z) && xor r ro) ((!ro) && xor z zo) := by
  cases r <;> cases z <;> cases ro <;> cases zo <;> rfl

/-- Literal physical mismatch recurrence. The local agreement premise is
enough; the following theorem obtains it from eventual center periodicity. -/
theorem mismatch_step {Q t : Nat} (hQt : Q≤t)
    (hc : cell t 0=cell (t-Q) 0) :
    mismatch Q (t+1)=xor (persists t && mismatch Q t) (forcing Q t) := by
  unfold mismatch persists forcing
  rw [show t+1-Q=(t-Q)+1 by omega]
  change xor (xor (cell t 0) (cell t 1 || cell t 2))
    (xor (cell (t-Q) 0) (cell (t-Q) 1 || cell (t-Q) 2)) = _
  rw [hc]
  have cancel (a b c : Bool) : xor (xor a b) (xor a c)=xor b c := by
    cases a <;> cases b <;> cases c <;> rfl
  rw [cancel, or_difference]

theorem periodic_mismatch_step {T Q : Nat}
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0)
    (t : Nat) (ht : T+Q≤t) :
    mismatch Q (t+1)=xor (persists t && mismatch Q t) (forcing Q t) := by
  apply mismatch_step (by omega)
  have hh := hc (t-Q) (by omega)
  simpa only [show t-Q+Q=t by omega] using hh

/-- On the valid time domain the masked defect is exactly a defect of the
effective OR boundary, not a defect of an unrelated moving observation. -/
theorem maskedDefect_eq_or_difference {T Q : Nat}
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0)
    (t : Nat) (ht : T+Q≤t) :
    maskedDefect Q t = xor (Rule30MaskedJen.orCol 0 t) (Rule30MaskedJen.orCol 0 (t-Q)) := by
  have he := hc (t-Q) (by omega)
  rw [show t-Q+Q=t by omega] at he
  unfold maskedDefect Rule30MaskedJen.orCol
  rw [he]
  simp only [Int.zero_add]
  cases cell (t-Q) 0 <;> cases cell t 1 <;> cases cell (t-Q) 1 <;> rfl

end Rule30PhysicalDefectBudgetResearch
