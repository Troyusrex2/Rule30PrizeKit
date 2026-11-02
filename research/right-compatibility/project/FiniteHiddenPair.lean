module
public import PeriodicHiddenPair
@[expose] public section
namespace FiniteHiddenPair
open Ruliology.CellularAutomata Rule30DrivenLeft Rule30DrivenMaskTransport
open PeriodicHiddenPair

def cut (H : Nat) (b : Bool) (p : Int) : Bool :=
  if p < -((H+7 : Nat) : Int) then false
  else if p = -((H+7 : Nat) : Int) then true else start b p

theorem cut_finite (H : Nat) (b : Bool) : FiniteNonzeroLeft (cut H b) := by
  refine ⟨H+7,by omega,?_,?_⟩
  · intro p hp; simp only [cut,ite_eq_left hp]
  · simp [cut]

theorem cut_matches (H : Nat) (b : Bool) (t : Nat) (ht : t≤H)
    (k : Nat) (hk : 0<k) (hk6 : k≤6) :
    L (effective driver) (cut H b) t (-(k : Int)) = profile b t k := by
  have hpref : ∀ p : Int, -((H+5+1 : Nat) : Int)≤p → p<0 → cut H b p=start b p := by
    intro p hp hn
    simp only [cut,ite_eq_right (show ¬p < -((H+7 : Nat) : Int) by omega),
      ite_eq_right (show ¬p = -((H+7 : Nat) : Int) by omega)]
  have h := light_cone (c:=effective driver) hpref t (by omega) (-(k : Int)) (by omega) (by omega)
  exact h.trans (actual_evolution b t k)

theorem starts_common (p : Int) (hp : p≤ -6) : start false p=start true p := by
  have hk : 6≤p.natAbs := by cases p <;> simp_all <;> omega
  simp [start,profile,show ¬p.natAbs=0 by omega,show ¬p.natAbs<6 by omega]

theorem cut_initial_common (H : Nat) (p : Int) (hp : p≤ -6) : cut H false p=cut H true p := by
  simp only [cut]
  split
  · rfl
  · split
    · rfl
    · exact starts_common p hp

theorem cut_common (H : Nat) : ∀ t, t≤H → ∀ p : Int, p≤ -6 →
    L (effective driver) (cut H false) t p = L (effective driver) (cut H true) t p := by
  intro t
  induction t with
  | zero =>
    intro ht p hp
    rw [L_zero (by omega),L_zero (by omega)]
    exact cut_initial_common H p hp
  | succ t ih =>
    intro ht p hp
    by_cases he : p= -6
    · subst p
      change L (effective driver) (cut H false) (t+1) (-((6 : Nat) : Int)) =
        L (effective driver) (cut H true) (t+1) (-((6 : Nat) : Int))
      rw [cut_matches H false (t+1) ht 6 (by decide) (by decide),
        cut_matches H true (t+1) ht 6 (by decide) (by decide)]
      rfl
    · rw [L_succ (by omega),L_succ (by omega),ih (by omega) (p-1) (by omega),
        ih (by omega) p hp,ih (by omega) (p+1) (by omega)]

theorem cut_pins (H : Nat) (b : Bool) (t : Nat) (ht : t≤H) (hc : driver t=true) :
    L (effective driver) (cut H b) t (-1)= !driver (t+1) := by
  change L (effective driver) (cut H b) t (-((1 : Nat) : Int))= !driver (t+1)
  rw [cut_matches H b t ht 1 (by decide) (by decide)]
  have h := pinned_forever b t hc
  rw [show (-1 : Int)= -((1 : Nat) : Int) by rfl,actual_evolution] at h
  exact h

theorem cut_distinct (H t : Nat) (ht : t≤H) : ∃ k : Nat, 0<k ∧ k<6 ∧
    L (effective driver) (cut H false) t (-(k : Int)) ≠
    L (effective driver) (cut H true) t (-(k : Int)) := by
  obtain ⟨k,hk,hk6,hd⟩:=distinct_forever t
  refine ⟨k,hk,hk6,?_⟩
  rw [cut_matches H false t ht k hk (by omega),cut_matches H true t ht k hk (by omega)]
  simpa only [actual_evolution] using hd

theorem initial_single_defect (H : Nat) (p : Int) (hp : p<0) :
    (cut H false p ≠ cut H true p) ↔ p= -3 := by
  by_cases hfar : p≤ -6
  · rw [cut_initial_common H p hfar]
    simp [show ¬p= -3 by omega]
  · have hcut (b : Bool) : cut H b p=start b p := by
      simp only [cut,
        ite_eq_right (show ¬p < -((H+7 : Nat) : Int) by omega),
        ite_eq_right (show ¬p = -((H+7 : Nat) : Int) by omega)]
    rw [hcut false,hcut true]
    have cases : p= -1 ∨ p= -2 ∨ p= -3 ∨ p= -4 ∨ p= -5 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl
    all_goals decide

/-- Fixed period and a fixed five-cell defect region admit arbitrarily long pinned,
unmerged finite-start trajectories. The common finite start depends on H. -/
theorem arbitrarily_long_hidden_pairs (H : Nat) :
    ∃ s r : Int → Bool, FiniteNonzeroLeft s ∧ FiniteNonzeroLeft r ∧
      (∀ t,t≤H → driver t=true →
        L (effective driver) s t (-1)= !driver (t+1) ∧
        L (effective driver) r t (-1)= !driver (t+1)) ∧
      (∀ t,t≤H → ∃ k : Nat,0<k ∧ k<6 ∧
        L (effective driver) s t (-(k : Int)) ≠ L (effective driver) r t (-(k : Int))) ∧
      (∀ t,t≤H → ∀ p : Int,p≤ -6 → L (effective driver) s t p=L (effective driver) r t p) := by
  refine ⟨cut H false,cut H true,cut_finite H false,cut_finite H true,?_,cut_distinct H,cut_common H⟩
  intro t ht hc
  exact ⟨cut_pins H false t ht hc,cut_pins H true t ht hc⟩

#print axioms arbitrarily_long_hidden_pairs
#print axioms initial_single_defect
end FiniteHiddenPair
