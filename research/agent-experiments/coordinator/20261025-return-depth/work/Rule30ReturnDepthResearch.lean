module
public import Rule30DyadicSourceResearch
public import Mathlib.Data.Nat.Find

/-! The least right-edge bit not returned after H steps, defined on the
actual seed. It is finite, and provides a true prefix period below the cut
and an exact bit flip at the cut. No center nonperiodicity is claimed. -/
@[expose] public section
namespace Rule30ReturnDepthResearch
open Ruliology.CellularAutomata Rule30Diagonals Rule30DyadicSourceResearch

theorem changed_before_left_edge (H : Nat) (hp : 0<H) :
    R (2*H-1) H ≠ R (2*H-1) 0 := by
  have hz : R (2*H-1) 0=false := R_at_zero _ (by omega)
  have he : R (2*H-1) H=true := by
    have h := D_one (H-1)
    rw [show H-1+1=H by omega] at h
    simpa [R,D,show (H:Int)-(2*H-1:Nat) = 1-(H:Int) by omega] using h
  rw [he,hz]
  decide

theorem exists_changed (H : Nat) (hp : 0<H) : ∃ d, R d H ≠ R d 0 :=
  ⟨2*H-1,changed_before_left_edge H hp⟩

noncomputable def cut (H : Nat) (hp : 0<H) : Nat := Nat.find (exists_changed H hp)

theorem cut_changed (H : Nat) (hp : 0<H) : R (cut H hp) H ≠ R (cut H hp) 0 :=
  Nat.find_spec (exists_changed H hp)

theorem before_cut (H : Nat) (hp : 0<H) (j : Nat) (hj : j<cut H hp) : R j H=R j 0 := by
  have h := Nat.find_min (exists_changed H hp) hj
  exact not_ne_iff.mp h

theorem cut_pos (H : Nat) (hp : 0<H) : 0<cut H hp := by
  have h := cut_changed H hp
  by_cases hz : cut H hp=0
  · rw [hz,R_zero,R_zero] at h
    contradiction
  · omega

theorem cut_bound (H : Nat) (hp : 0<H) : cut H hp≤2*H-1 :=
  Nat.find_min' (exists_changed H hp) (changed_before_left_edge H hp)

theorem cut_bit_true (H : Nat) (hp : 0<H) : R (cut H hp) H=true := by
  have h := cut_changed H hp
  rw [R_at_zero _ (cut_pos H hp)] at h
  cases hb : R (cut H hp) H <;> simp_all

theorem prefix_period (H : Nat) (hp : 0<H) (t : Nat) :
    ∀ j, j<cut H hp → R j (t+H)=R j t := by
  induction t with
  | zero => intro j hj; simpa using before_cut H hp j hj
  | succ t ih =>
    intro j hj
    rw [show t+1+H=(t+H)+1 by omega]
    cases j with
    | zero => rw [R_zero,R_zero]
    | succ j =>
      cases j with
      | zero => rw [R_one_succ,R_one_succ,ih 1 hj]
      | succ j => rw [R_step,R_step,ih (j+2) hj,ih (j+1) (by omega),ih j (by omega)]

theorem cut_bit_flip (H : Nat) (hp : 0<H) :
    ∀ t, R (cut H hp) (t+H)=!R (cut H hp) t := by
  intro t
  induction t with
  | zero => simp [cut_bit_true H hp,R_at_zero _ (cut_pos H hp)]
  | succ t ih =>
    rw [show t+1+H=(t+H)+1 by omega]
    by_cases h1 : cut H hp=1
    · rw [h1,R_one_succ,R_one_succ]
      rw [h1] at ih
      rw [ih]
    · have hd : 2≤cut H hp := by have := cut_pos H hp; omega
      have hc : cut H hp=(cut H hp-2)+2 := by omega
      have hstep : ∀ u, R (cut H hp) (u+1)=
          xor (R (cut H hp) u) (R (cut H hp-1) u || R (cut H hp-2) u) := by
        intro u
        have h := R_step (cut H hp-2) u
        rw [←hc,show cut H hp-2+1=cut H hp-1 by omega] at h
        exact h
      rw [hstep,hstep,ih,prefix_period H hp t (cut H hp-1) (by omega),
        prefix_period H hp t (cut H hp-2) (by omega)]
      cases R (cut H hp) t <;>
        cases (R (cut H hp-1) t || R (cut H hp-2) t) <;> rfl

theorem prefix_last_phase (H : Nat) (hp : 0<H) (j : Nat) (hj : j<cut H hp) :
    R j (H-1)=true := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => exact R_zero _
    | succ j =>
      cases j with
      | zero =>
        have h := R_one_succ (H-1)
        rw [show H-1+1=H by omega,before_cut H hp 1 hj,R_at_zero 1 (by omega)] at h
        cases hb : R 1 (H-1) <;> simp_all
      | succ j =>
        have low := ih (j+1) (by omega) (by omega)
        have h := R_step j (H-1)
        rw [show H-1+1=H by omega,before_cut H hp (j+2) hj,R_at_zero _ (by omega),low] at h
        cases hb : R (j+2) (H-1) <;> simp_all

theorem source_prefix_period (H : Nat) (hp : 0<H) (d t : Nat) (hd : d<cut H hp) :
    source d (t+H)=source d t := by
  by_cases hz : d=0
  · simp [hz,source_outer]
  · simp [source,hz,prefix_period H hp t d hd,prefix_period H hp t (d-1) (by omega)]

theorem source_prefix_last (H : Nat) (hp : 0<H) (d : Nat)
    (hd0 : 0<d) (hd : d<cut H hp) : source d (H-1)=false := by
  simp [source,Nat.ne_of_gt hd0,prefix_last_phase H hp d hd,
    prefix_last_phase H hp (d-1) (by omega)]

theorem source_prefix_window (H : Nat) (hp : 0<H) (d v : Nat)
    (hd : d<cut H hp) (hv : 2*v<d) : source d (H+v)=false := by
  rw [Nat.add_comm,source_prefix_period H hp d v hd]
  exact source_zero_before_cone d v hv

theorem cut_last_phase (H : Nat) (hp : 0<H) : R (cut H hp) (H-1)=false := by
  by_cases h1 : cut H hp=1
  · rw [h1]
    have ht : R 1 H=true := by simpa only [h1] using cut_bit_true H hp
    have h := R_one_succ (H-1)
    rw [show H-1+1=H by omega,ht] at h
    cases hb : R 1 (H-1)
    · rfl
    · simpa only [hb,Bool.not_true] using h
  · have hd : 2≤cut H hp := by have := cut_pos H hp; omega
    have hc : cut H hp=(cut H hp-2)+2 := by omega
    have low := prefix_last_phase H hp (cut H hp-2+1) (by omega)
    have h := R_step (cut H hp-2) (H-1)
    rw [show H-1+1=H by omega,←hc,cut_bit_true H hp,low] at h
    cases hb : R (cut H hp) (H-1)
    · rfl
    · simpa only [hb,Bool.true_or,Bool.true_xor,Bool.not_true] using h

theorem source_cut_last (H : Nat) (hp : 0<H) : source (cut H hp) (H-1)=false := by
  rw [source,ite_eq_right (Nat.ne_of_gt (cut_pos H hp)),cut_last_phase H hp]
  rfl

theorem source_cut_window (H : Nat) (hp : 0<H) (v : Nat) (hv : 2*v+1<cut H hp) :
    source (cut H hp) (H+v)=true := by
  have hz : R (cut H hp) v=false := Rule30Jen.cell_eq_false_of_lt _ _ (by omega)
  have hl : R (cut H hp-1) v=false := Rule30Jen.cell_eq_false_of_lt _ _ (by omega)
  rw [source,ite_eq_right (Nat.ne_of_gt (cut_pos H hp)),Nat.add_comm,
    cut_bit_flip H hp,prefix_period H hp v (cut H hp-1) (by have := cut_pos H hp; omega),hz,hl]
  rfl

end Rule30ReturnDepthResearch
