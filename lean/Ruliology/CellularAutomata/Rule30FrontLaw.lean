module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Rule30FrontLaw

A one-bit defect determines the onset of periodicity of a driven diagonal. The recursively defined frontBound has a period-sum bound.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30FrontLaw

open Rule30Diagonals

section Generic
variable {x a b : Nat → Bool}

theorem periodic_two {f : Nat → Bool} {s L : Nat} (hf : ∀ t, s ≤ t → f (t + L) = f t) :
    ∀ t, s ≤ t → f (t + 2 * L) = f t := by
  intro t ht
  rw [Nat.two_mul, ← Nat.add_assoc, hf _ (by omega), hf t ht]

theorem reset_periodic {s L : Nat}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (ha : ∀ t, s ≤ t → a (t + L) = a t) (hb : ∀ t, s ≤ t → b (t + L) = b t)
    {s0 : Nat} (hs : s ≤ s0) (hreset : b s0 = true) :
    ∀ t, s0 + 1 ≤ t → x (t + L) = x t := by
  have key : ∀ n, x (s0 + 1 + n + L) = x (s0 + 1 + n) := by
    intro n
    induction n with
    | zero =>
      rw [show s0 + 1 + 0 + L = (s0 + L) + 1 by omega, show s0 + 1 + 0 = s0 + 1 by omega, hx, hx,
        ha s0 hs, hb s0 hs, hreset]
      simp
    | succ n ih =>
      rw [show s0 + 1 + (n + 1) + L = (s0 + 1 + n + L) + 1 by omega,
        show s0 + 1 + (n + 1) = (s0 + 1 + n) + 1 by omega, hx, hx, ha _ (by omega),
        hb _ (by omega), ih]
  intro t ht
  obtain ⟨n, rfl⟩ : ∃ n, t = s0 + 1 + n := ⟨t - (s0 + 1), by omega⟩
  exact key n

theorem defect_step {s L w : Nat}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (ha : ∀ t, s ≤ t → a (t + L) = a t) (hb : ∀ t, s ≤ t → b (t + L) = b t)
    (hw : s ≤ w) (hbw : b w = false) :
    xor (x (w + 1 + L)) (x (w + 1)) = xor (x (w + L)) (x w) := by
  rw [show w + 1 + L = (w + L) + 1 by omega, hx, hx, ha w hw, hb w hw, hbw]
  cases a w <;> cases x w <;> cases x (w + L) <;> rfl

theorem defect_const {s L e : Nat}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (ha : ∀ t, s ≤ t → a (t + L) = a t) (hb : ∀ t, s ≤ t → b (t + L) = b t)
    (hwhite : ∀ w, s ≤ w → w < e → b w = false) :
    ∀ t, s ≤ t → t ≤ e → xor (x (t + L)) (x t) = xor (x (s + L)) (x s) := by
  have key : ∀ n, s + n ≤ e → xor (x (s + n + L)) (x (s + n)) = xor (x (s + L)) (x s) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [show s + (n + 1) = s + n + 1 by omega,
        defect_step hx ha hb (by omega) (hwhite _ (by omega) (by omega)), ih (by omega)]
  intro t hst hte
  obtain ⟨n, rfl⟩ : ∃ n, t = s + n := ⟨t - s, by omega⟩
  exact key n hte

theorem front_match {s L s0 : Nat}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (ha : ∀ t, s ≤ t → a (t + L) = a t) (hb : ∀ t, s ≤ t → b (t + L) = b t)
    (hs : s ≤ s0) (hreset : b s0 = true) (hwhite : ∀ w, s ≤ w → w < s0 → b w = false)
    (hm : x (s + L) = x s) :
    ∀ t, s ≤ t → x (t + L) = x t := by
  intro t ht
  by_cases h : t ≤ s0
  · have e := defect_const hx ha hb hwhite t ht h
    rw [hm] at e
    revert e; cases x (t + L) <;> cases x t <;> cases x s <;> simp
  · exact reset_periodic hx ha hb hs hreset t (by omega)

theorem front_mismatch {s L s0 : Nat}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (ha : ∀ t, s ≤ t → a (t + L) = a t) (hb : ∀ t, s ≤ t → b (t + L) = b t)
    (hwhite : ∀ w, s ≤ w → w < s0 → b w = false)
    (hm : x (s + L) ≠ x s) :
    ∀ t, s ≤ t → t ≤ s0 → x (t + L) ≠ x t := by
  intro t ht hts
  have e := defect_const hx ha hb hwhite t ht hts
  revert e hm; cases x (t + L) <;> cases x t <;> cases x s <;> cases x (s + L) <;> simp

theorem white_double {s L : Nat}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (ha : ∀ t, s ≤ t → a (t + L) = a t) (hb : ∀ t, s ≤ t → b (t + L) = b t)
    (hwhite : ∀ w, s ≤ w → b w = false) :
    ∀ t, s ≤ t → x (t + 2 * L) = x t := by
  intro t ht
  have e1 := defect_const (e := t + L) hx ha hb (fun w hw _ => hwhite w hw) t ht (by omega)
  have e2 := defect_const (e := t + L) hx ha hb (fun w hw _ => hwhite w hw) (t + L) (by omega)
    (by omega)
  rw [show t + 2 * L = t + L + L by omega]
  revert e1 e2
  cases x (t + L + L) <;> cases x (t + L) <;> cases x t <;> cases x (s + L) <;> cases x s <;> simp

end Generic

theorem D_front_law {j s L s0 : Nat}
    (ha : ∀ t, s ≤ t → D j (t + L) = D j t) (hb : ∀ t, s ≤ t → D (j + 1) (t + L) = D (j + 1) t)
    (hs : s ≤ s0) (hreset : D (j + 1) s0 = true)
    (hwhite : ∀ w, s ≤ w → w < s0 → D (j + 1) w = false) :
    (D (j + 2) (s + L) = D (j + 2) s → ∀ t, s ≤ t → D (j + 2) (t + L) = D (j + 2) t) ∧
    (D (j + 2) (s + L) ≠ D (j + 2) s →
      (∀ t, s ≤ t → t ≤ s0 → D (j + 2) (t + L) ≠ D (j + 2) t) ∧
      (∀ t, s0 + 1 ≤ t → D (j + 2) (t + L) = D (j + 2) t)) :=
  ⟨front_match (x := D (j + 2)) (D_step j) ha hb hs hreset hwhite,
   fun hm => ⟨front_mismatch (x := D (j + 2)) (D_step j) ha hb hwhite hm,
     reset_periodic (x := D (j + 2)) (D_step j) ha hb hs hreset⟩⟩

theorem exists_least {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  obtain ⟨n, hn⟩ := h
  revert hn
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hc : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hPm⟩ := hc
      exact ih m hm hPm
    · exact ⟨n, hn, fun m hm hPm => hc ⟨m, hm, hPm⟩⟩

open Classical in

noncomputable def frontBound : Nat → Nat
  | 0 => 0
  | 1 => 1
  | j + 2 =>
    if h : ∃ u, max (frontBound j) (frontBound (j + 1)) ≤ u ∧ D (j + 1) u = true then
      Classical.choose (exists_least h) + 1
    else max (frontBound j) (frontBound (j + 1))

theorem frontBound_reset {j : Nat}
    (h : ∃ u, max (frontBound j) (frontBound (j + 1)) ≤ u ∧ D (j + 1) u = true) :
    ∃ u, max (frontBound j) (frontBound (j + 1)) ≤ u ∧ D (j + 1) u = true ∧
      (∀ w, max (frontBound j) (frontBound (j + 1)) ≤ w → w < u → D (j + 1) w = false) ∧
      frontBound (j + 2) = u + 1 := by
  have hs := Classical.choose_spec (exists_least h)
  refine ⟨Classical.choose (exists_least h), hs.1.1, hs.1.2, ?_, ?_⟩
  · intro w hw hlt
    cases hD : D (j + 1) w
    · rfl
    · exact absurd ⟨hw, hD⟩ (hs.2 w hlt)
  · simp only [frontBound, h]
    rfl

theorem frontBound_white {j : Nat}
    (h : ¬ ∃ u, max (frontBound j) (frontBound (j + 1)) ≤ u ∧ D (j + 1) u = true) :
    frontBound (j + 2) = max (frontBound j) (frontBound (j + 1)) := by
  simp only [frontBound, h]; rfl

theorem D_periodic_from_frontBound :
    ∀ j t, frontBound j ≤ t → D j (t + 2 ^ j) = D j t := by
  have pair : ∀ j, (∀ t, frontBound j ≤ t → D j (t + 2 ^ j) = D j t) ∧
      (∀ t, frontBound (j + 1) ≤ t → D (j + 1) (t + 2 ^ (j + 1)) = D (j + 1) t) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun t _ => by rw [D_zero, D_zero], fun t ht => ?_⟩
      have ht' : 1 ≤ t := ht
      obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
      rw [show n + 1 + 2 ^ (0 + 1) = (n + 2) + 1 by simp, D_one, D_one]
    | succ j ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1, ?_⟩
      have ha : ∀ t, max (frontBound j) (frontBound (j + 1)) ≤ t → D j (t + 2 ^ (j + 1)) = D j t := by
        intro t ht
        rw [Nat.pow_succ, Nat.mul_comm]
        exact periodic_two h0 t (by omega)
      have hb : ∀ t, max (frontBound j) (frontBound (j + 1)) ≤ t → D (j + 1) (t + 2 ^ (j + 1)) = D (j + 1) t :=
        fun t ht => h1 t (by omega)
      intro t ht
      rw [show j + 1 + 1 = j + 2 by omega] at ht ⊢
      rw [show 2 ^ (j + 2) = 2 * 2 ^ (j + 1) by rw [Nat.pow_succ, Nat.mul_comm]]
      by_cases h : ∃ u, max (frontBound j) (frontBound (j + 1)) ≤ u ∧ D (j + 1) u = true
      · obtain ⟨u, hu, hblack, _, hR⟩ := frontBound_reset h
        have hper := reset_periodic (x := D (j + 2)) (D_step j) ha hb hu hblack
        exact periodic_two hper t (by omega)
      · rw [frontBound_white h] at ht
        have hw : ∀ w, max (frontBound j) (frontBound (j + 1)) ≤ w → D (j + 1) w = false := by
          intro w hw
          cases hD : D (j + 1) w
          · rfl
          · exact absurd ⟨w, hw, hD⟩ h
        exact white_double (x := D (j + 2)) (D_step j) ha hb hw t ht
  intro j
  exact (pair j).1

theorem frontBound_step_reset {j : Nat}
    (h : ∃ u, max (frontBound j) (frontBound (j + 1)) ≤ u ∧ D (j + 1) u = true) :
    max (frontBound j) (frontBound (j + 1)) < frontBound (j + 2) := by
  obtain ⟨u, hu, _, _, hR⟩ := frontBound_reset h
  omega

theorem D_shift_mul {j : Nat} : ∀ n t, frontBound j ≤ t → D j (t + n * 2 ^ j) = D j t := by
  intro n
  induction n with
  | zero => intro t _; simp
  | succ n ih =>
    intro t ht
    rw [Nat.succ_mul, ← Nat.add_assoc, D_periodic_from_frontBound j _ (by omega), ih t ht]

theorem D_period_from_frontBound {j P T : Nat} (hP : ∀ t, T ≤ t → D j (t + P) = D j t) :
    ∀ t, frontBound j ≤ t → D j (t + P) = D j t := by
  intro t ht
  have hT : T ≤ t + T * 2 ^ j := by
    have : T ≤ T * 2 ^ j := Nat.le_mul_of_pos_right T (Nat.pow_pos (by decide : 0 < 2))
    omega
  rw [← D_shift_mul (j := j) T (t + P) (by omega), show t + P + T * 2 ^ j = t + T * 2 ^ j + P by omega,
    hP _ hT, D_shift_mul T t ht]

theorem frontBound_step_le {j P T : Nat} (hP0 : 0 < P)
    (hP : ∀ t, T ≤ t → D (j + 1) (t + P) = D (j + 1) t) :
    frontBound (j + 2) ≤ max (frontBound j) (frontBound (j + 1)) + P := by
  by_cases h : ∃ u, max (frontBound j) (frontBound (j + 1)) ≤ u ∧ D (j + 1) u = true
  · obtain ⟨u, hu, hblack, hwhite, hR⟩ := frontBound_reset h
    rw [hR]
    apply Nat.succ_le_of_lt
    apply Nat.lt_of_not_le
    intro hge
    have hper := D_period_from_frontBound hP (u - P) (by omega)
    rw [show u - P + P = u by omega, hblack] at hper
    have := hwhite (u - P) (by omega) (by omega)
    rw [this] at hper
    exact Bool.noConfusion hper
  · rw [frontBound_white h]; omega

def periodSum (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => periodSum f k + f k

theorem periodSum_mono (f : Nat → Nat) (k : Nat) : periodSum f k ≤ periodSum f (k + 1) := by
  simp only [periodSum]; omega

theorem frontBound_le_periodSum {f : Nat → Nat} (hf0 : ∀ j, 0 < f j)
    (hf : ∀ j, ∃ T, ∀ t, T ≤ t → D j (t + f j) = D j t) :
    ∀ k, frontBound k ≤ periodSum f k := by
  have pair : ∀ k, frontBound k ≤ periodSum f k ∧ frontBound (k + 1) ≤ periodSum f (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp [frontBound, periodSum], ?_⟩
      show 1 ≤ periodSum f 0 + f 0
      simp [periodSum]
    | succ k ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1, ?_⟩
      obtain ⟨T, hT⟩ := hf (k + 1)
      have hstep := frontBound_step_le (j := k) (hf0 (k + 1)) hT
      have hm := periodSum_mono f k
      show frontBound (k + 2) ≤ periodSum f (k + 1) + f (k + 1)
      omega
  exact fun k => (pair k).1

theorem frontBound_le_linear {π f : Nat → Nat} (hπ0 : ∀ j, 0 < π j)
    (hπ : ∀ j, ∃ T, ∀ t, T ≤ t → D j (t + π j) = D j t)
    (hle : ∀ j, π j ≤ f j) (hmono : ∀ i j, i ≤ j → f i ≤ f j) :
    ∀ k, frontBound k ≤ 1 + k * f k := by
  have hs : ∀ k n, k ≤ n → periodSum π k ≤ 1 + k * f n := by
    intro k
    induction k with
    | zero => intro n _; simp [periodSum]
    | succ k ih =>
      intro n hn
      have := ih n (by omega)
      have := hmono k n (by omega)
      have := hle k
      simp only [periodSum, Nat.succ_mul]
      omega
  exact fun k => Nat.le_trans (frontBound_le_periodSum hπ0 hπ k) (hs k k (Nat.le_refl k))

end Rule30FrontLaw
end Ruliology.CellularAutomata
