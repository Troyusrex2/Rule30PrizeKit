module
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! A short legal boundary window forces the two inverse heads to coalesce.
This does not prove that either inverse has finite support. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GateInverseMergeResearch
open Rule30ZeroBoundary

def words : List Nat := [8,9,16,18,33,36,66,72,132,144]

def phase (w t : Nat) : Bool :=
  if t % 2 = 0 then true else !(Nat.testBit w (t / 2))

def template (w : Nat) : Nat → Bool := lam (phase w)

/-- Eight forced black readings and the interleaved complementary gate word. -/
def LocalWindow (y : Nat → Bool) : Prop :=
  ∃ w, w ∈ words ∧ ∀ t, t < 16 → zrow y t 1 = phase w t

theorem back_congr_pair (b : Bool) (y z : Nat → Bool) (n : Nat)
    (h : ∀ k, 1 ≤ k → k ≤ n → y k = z k) :
    back b y n = back b z n ∧ back b y (n+1) = back b z (n+1) := by
  induction n with
  | zero => constructor <;> rfl
  | succ n ih =>
      obtain ⟨h0,h1⟩ := ih (fun k hk hn => h k hk (by omega))
      constructor
      · exact h1
      · change xor (y (n+1)) (back b y (n+1) || back b y n) =
          xor (z (n+1)) (back b z (n+1) || back b z n)
        rw [h (n+1) (by omega) (by omega), h0, h1]

theorem back_tail_of_pair (y : Nat → Bool) (b c : Bool) (n : Nat)
    (h0 : back b y n = back c y n)
    (h1 : back b y (n+1) = back c y (n+1)) :
    ∀ k, n ≤ k → back b y k = back c y k := by
  have key : ∀ j, back b y (n+j) = back c y (n+j) ∧
      back b y (n+j+1) = back c y (n+j+1) := by
    intro j
    induction j with
    | zero => simpa using And.intro h0 h1
    | succ j ih =>
        constructor
        · simpa only [Nat.add_assoc] using ih.2
        · change xor (y (n+j+1)) (back b y (n+j+1) || back b y (n+j)) =
            xor (y (n+j+1)) (back c y (n+j+1) || back c y (n+j))
          rw [ih.1, ih.2]
  intro k hk
  simpa only [Nat.add_sub_of_le hk] using (key (k-n)).1

theorem row_eq_template (y : Nat → Bool) (w : Nat)
    (h : ∀ t, t < 16 → zrow y t 1 = phase w t)
    (k : Nat) (hk : 1 ≤ k) (hbound : k ≤ 16) : y k = template w k := by
  change y k = recon (phase w) k 0
  calc
    y k = recon (fun t => zrow y t 1) k 0 :=
      (zrow_zero_of_pos y hk).symm.trans (history_eq_recon y k 0)
    _ = recon (phase w) k 0 := by
      apply recon_local
      intro j hj
      simpa only [Nat.zero_add] using h j (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem merge_certificate (w : Nat) (hw : w ∈ words) :
    back false (template w) 11 = back true (template w) 11 ∧
    back false (template w) 12 = back true (template w) 12 := by
  simp [words] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem heads_agree_after_eleven (y : Nat → Bool) (h : LocalWindow y) :
    ∀ k, 11 ≤ k → back false y k = back true y k := by
  obtain ⟨w,hw,hy⟩ := h
  have same (b : Bool) : back b y 11 = back b (template w) 11 ∧
      back b y 12 = back b (template w) 12 :=
    back_congr_pair b y (template w) 11
      (fun k hk hn => row_eq_template y w hy k hk (by omega))
  obtain ⟨hc0,hc1⟩ := merge_certificate w hw
  apply back_tail_of_pair y false true 11
  · exact (same false).1.trans (hc0.trans (same true).1.symm)
  · exact (same false).2.trans (hc1.trans (same true).2.symm)

theorem finite_head_independent (y : Nat → Bool) (h : LocalWindow y) :
    FinSupp (back false y) ↔ FinSupp (back true y) := by
  have he := heads_agree_after_eleven y h
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨max W 11, fun k hk => ?_⟩
    rw [← he k (by omega)]
    exact hW k (by omega)
  · rintro ⟨W,hW⟩
    refine ⟨max W 11, fun k hk => ?_⟩
    rw [he k (by omega)]
    exact hW k (by omega)

theorem finite_preimage_iff_head_true (y : Nat → Bool) (h : LocalWindow y) :
    (∃ b : Bool, FinSupp (back b y)) ↔ FinSupp (back true y) := by
  constructor
  · rintro ⟨b,hb⟩
    cases b with
    | false => exact (finite_head_independent y h).1 hb
    | true => exact hb
  · intro ht
    exact ⟨true,ht⟩

theorem back_trace (b : Bool) (L : Nat → Bool) (t k : Nat) :
    zrow (back b L) (t+1) k = zrow L t k := by
  calc
    zrow (back b L) (t+1) k = zrow (zrow (back b L) 1) t k := by
      simpa only [Nat.add_comm] using zrow_shift (back b L) 1 t k
    _ = zrow L t k := zrow_congr (zrow_back b L) t k

/-- The first eight even readings encode a legal gate, and the odd readings are black. -/
def OddGateWindow (L : Nat → Bool) : Prop :=
  ∃ w, w ∈ words ∧
    (∀ r, r < 8 → zrow L (2*r+1) 1 = true) ∧
    (∀ r, r < 8 → zrow L (2*r) 1 = !(Nat.testBit w r))

theorem first_inverse_window (L : Nat → Bool) (h : OddGateWindow L) :
    LocalWindow (back true L) := by
  obtain ⟨w,hw,ho,he⟩ := h
  refine ⟨w,hw,fun t ht => ?_⟩
  by_cases hz : t = 0
  · subst t
    rfl
  · have hp : 1 ≤ t := by omega
    have hb := back_trace true L (t-1) 1
    rw [show t-1+1=t by omega] at hb
    rw [hb]
    unfold phase
    by_cases hm : t % 2 = 0
    · rw [ite_eq_left hm]
      have hr : 1 ≤ t/2 := by omega
      have hx : t-1 = 2*(t/2-1)+1 := by omega
      rw [hx]
      exact ho (t/2-1) (by omega)
    · rw [ite_eq_right hm]
      have hx : t-1 = 2*(t/2) := by omega
      rw [hx]
      exact he (t/2) (by omega)

theorem second_inverse_heads_agree (L : Nat → Bool) (h : OddGateWindow L) :
    ∀ k, 11 ≤ k → back false (back true L) k = back true (back true L) k :=
  heads_agree_after_eleven (back true L) (first_inverse_window L h)

theorem second_inverse_finite_head_independent (L : Nat → Bool) (h : OddGateWindow L) :
    FinSupp (back false (back true L)) ↔ FinSupp (back true (back true L)) :=
  finite_head_independent (back true L) (first_inverse_window L h)

def oddPhase (w t : Nat) : Bool :=
  if t % 2 = 0 then !(Nat.testBit w (t/2)) else true

def oddTemplate (w : Nat) : Nat → Bool := lam (oddPhase w)

theorem odd_window_match (L : Nat → Bool) (w : Nat)
    (ho : ∀ r, r < 8 → zrow L (2*r+1) 1 = true)
    (he : ∀ r, r < 8 → zrow L (2*r) 1 = !(Nat.testBit w r)) :
    ∀ t, t < 16 → zrow L t 1 = oddPhase w t := by
  intro t ht
  unfold oddPhase
  by_cases hm : t%2=0
  · rw [ite_eq_left hm]
    have hx : t=2*(t/2) := by omega
    exact (congrArg (fun s => zrow L s 1) hx).trans (he (t/2) (by omega))
  · rw [ite_eq_right hm]
    have hx : t=2*(t/2)+1 := by omega
    rw [hx]
    exact ho (t/2) (by omega)

theorem row_eq_odd_template (L : Nat → Bool) (w : Nat)
    (h : ∀ t, t < 16 → zrow L t 1 = oddPhase w t)
    (k : Nat) (hk : 1 ≤ k) (hbound : k ≤ 16) : L k = oddTemplate w k := by
  change L k = recon (oddPhase w) k 0
  calc
    L k = recon (fun t => zrow L t 1) k 0 :=
      (zrow_zero_of_pos L hk).symm.trans (history_eq_recon L k 0)
    _ = recon (oddPhase w) k 0 := by
      apply recon_local
      intro j hj
      simpa only [Nat.zero_add] using h j (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem first_merge_certificate (w : Nat) (hw : w ∈ words) :
    back false (oddTemplate w) 7 = back true (oddTemplate w) 7 ∧
    back false (oddTemplate w) 8 = back true (oddTemplate w) 8 := by
  simp [words] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem first_inverse_heads_agree (L : Nat → Bool) (h : OddGateWindow L) :
    ∀ k, 7 ≤ k → back false L k = back true L k := by
  obtain ⟨w,hw,ho,he⟩ := h
  have hh := odd_window_match L w ho he
  have same (b : Bool) : back b L 7 = back b (oddTemplate w) 7 ∧
      back b L 8 = back b (oddTemplate w) 8 :=
    back_congr_pair b L (oddTemplate w) 7
      (fun k hk hn => row_eq_odd_template L w hh k hk (by omega))
  obtain ⟨hc0,hc1⟩ := first_merge_certificate w hw
  apply back_tail_of_pair L false true 7
  · exact (same false).1.trans (hc0.trans (same true).1.symm)
  · exact (same false).2.trans (hc1.trans (same true).2.symm)

theorem first_inverse_finite_head_independent (L : Nat → Bool) (h : OddGateWindow L) :
    FinSupp (back false L) ↔ FinSupp (back true L) := by
  have he := first_inverse_heads_agree L h
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨max W 7, fun k hk => ?_⟩
    rw [← he k (by omega)]
    exact hW k (by omega)
  · rintro ⟨W,hW⟩
    refine ⟨max W 7, fun k hk => ?_⟩
    rw [he k (by omega)]
    exact hW k (by omega)

theorem first_preimage_exists_iff_prescribed (L : Nat → Bool) (h : OddGateWindow L) :
    (∃ b : Bool, FinSupp (back b L)) ↔ FinSupp (back true L) := by
  constructor
  · rintro ⟨b,hb⟩
    cases b with
    | false => exact (first_inverse_finite_head_independent L h).1 hb
    | true => exact hb
  · intro ht
    exact ⟨true,ht⟩

end Ruliology.CellularAutomata.Rule30GateInverseMergeResearch
