module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
All-time common-gauge rigidity with a zero background. The auxiliary field
is not assumed to be a physical Rule30 history. This adapts the catalog's
XOR-rigidity gap argument, keeping an asymmetric black right endpoint.
No claim of a canonical center observer or Prize Problem 1 is made.
-/

@[expose] public section
namespace Rule30VacuumGaugeResearch
open Ruliology.CellularAutomata.Rule30Jen (rule)

def lin (a l c r : Bool) : Bool := xor (xor l c) ((!a) && r)

def Good (a b c d : Bool) : Prop := (a && d)=(c && b)

theorem good_self (a b : Bool) : Good a b a b := rfl
theorem good_symm : ∀ a b c d : Bool, Good a b c d → Good c d a b := by
  unfold Good; decide +kernel
theorem middle_zero : ∀ a b c d e f : Bool,
    ¬ Good a b e f → Good a b c d → Good c d e f → c=false ∧ d=false := by
  unfold Good; decide +kernel

theorem gap_two : ∀ a b d e f : Bool,
    Good (rule a false true) (lin false b false d)
      (rule false true e) (lin true false d f) → Good a b true d := by
  unfold Good; decide +kernel

namespace HalfLine
def Actual (A : Nat → Nat → Bool) : Prop :=
  ∀ t i, A (t+1) i=rule (A t i) (A t (i+1)) (A t (i+2))
def Driven (A h : Nat → Nat → Bool) : Prop :=
  ∀ t i, h (t+1) i=lin (A t (i+1)) (h t i) (h t (i+1)) (h t (i+2))
def Common (A h : Nat → Nat → Bool) : Prop :=
  ∀ t i, Good (A t i) (h t i) (A t (i+1)) (h t (i+1))
def CommonThrough (A h : Nat → Nat → Bool) (N : Nat) : Prop :=
  ∀ t, t ≤ N → ∀ i, Good (A t i) (h t i) (A t (i+1)) (h t (i+1))

/-- No physical-history premise on h. The right endpoint must be black in A. -/
theorem distant_good_right_black_through (A h : Nat → Nat → Bool)
    (ha : Actual A) (hh : Driven A h) (N : Nat) (hw : CommonThrough A h N) (d : Nat) :
    ∀ t p, t+d/2 ≤ N → A t (p+d)=true →
      Good (A t p) (h t p) (A t (p+d)) (h t (p+d)) := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro t p ht hblack
    by_cases hd0 : d=0
    · subst d; exact good_self _ _
    by_cases hd1 : d=1
    · subst d; exact hw t (by omega) p
    apply Classical.byContradiction
    intro bad
    have mid : ∀ k, p<k → k<p+d → A t k=false ∧ h t k=false := by
      intro k hpk hkq
      have hr := ih (p+d-k) (by omega) t k (by omega)
        (by simpa [show k+(p+d-k)=p+d by omega] using hblack)
      rw [show k+(p+d-k)=p+d by omega] at hr
      by_cases hak : A t k=true
      · have hl := ih (k-p) (by omega) t p (by omega)
          (by simpa [show p+(k-p)=k by omega] using hak)
        rw [show p+(k-p)=k by omega] at hl
        have hz := middle_zero _ _ _ _ _ _ bad hl hr
        rw [hak] at hz
        cases hz.1
      · have hak0 : A t k=false := by cases he : A t k <;> simp_all
        refine ⟨hak0, ?_⟩
        simpa [Good, hak0, hblack] using hr.symm
    by_cases hd2 : d=2
    · subst d
      obtain ⟨az,hz⟩ := mid (p+1) (by omega) (by omega)
      have hn := hw (t+1) (by omega) p
      rw [ha t p, hh t p, ha t (p+1), hh t (p+1), az,hz,
        show p+1+1=p+2 by omega, show p+1+2=p+3 by omega, hblack] at hn
      apply bad
      rw [hblack]
      exact gap_two (A t p) (h t p) (h t (p+2)) (A t (p+3)) (h t (p+3)) hn
    · obtain ⟨a1,h1⟩ := mid (p+1) (by omega) (by omega)
      obtain ⟨a2,h2⟩ := mid (p+2) (by omega) (by omega)
      obtain ⟨az,hz⟩ := mid (p+d-2) (by omega) (by omega)
      obtain ⟨az1,hz1⟩ := mid (p+d-1) (by omega) (by omega)
      have hnextblack : A (t+1) (p+(d-2))=true := by
        rw [show p+(d-2)=p+d-2 by omega, ha, az,
          show p+d-2+1=p+d-1 by omega, show p+d-2+2=p+d by omega, az1,hblack]
        rfl
      have hn := ih (d-2) (by omega) (t+1) p (by omega) hnextblack
      rw [show p+(d-2)=p+d-2 by omega, ha t p,hh t p,
        ha t (p+d-2),hh t (p+d-2), a1,h1,a2,h2,az,hz,
        show p+d-2+1=p+d-1 by omega, show p+d-2+2=p+d by omega,
        az1,hz1,hblack] at hn
      exact bad (by simpa [rule,lin,hblack] using hn)

theorem distant_good_right_black (A h : Nat → Nat → Bool)
    (ha : Actual A) (hh : Driven A h) (hw : Common A h) (d t p : Nat)
    (hblack : A t (p+d)=true) :
    Good (A t p) (h t p) (A t (p+d)) (h t (p+d)) :=
  distant_good_right_black_through A h ha hh (t+d/2) (fun s _ i => hw s i)
    d t p (by omega) hblack

theorem initial_phase (A h : Nat → Nat → Bool)
    (ha : Actual A) (hh : Driven A h) (hw : Common A h)
    (hs : ∀ i, (h 0 i && A 0 i)=h 0 i) :
    ∃ b : Bool, ∀ i, h 0 i=(b && A 0 i) := by
  by_cases hex : ∃ q, A 0 q=true
  · obtain ⟨q,hq⟩ := hex
    refine ⟨h 0 q, ?_⟩
    intro p
    cases hp : A 0 p with
    | false => simpa [hp] using (hs p).symm
    | true =>
      have hg : Good (A 0 p) (h 0 p) (A 0 q) (h 0 q) := by
        by_cases hle : p ≤ q
        · have hg := distant_good_right_black A h ha hh hw (q-p) 0 p
            (by simpa [Nat.add_sub_of_le hle] using hq)
          simpa [Nat.add_sub_of_le hle] using hg
        · have hg := distant_good_right_black A h ha hh hw (p-q) 0 q
            (by simpa [Nat.add_sub_of_le (by omega : q ≤ p)] using hp)
          apply good_symm
          simpa [Nat.add_sub_of_le (by omega : q ≤ p)] using hg
      simpa [Good,hp,hq] using hg.symm
  · refine ⟨false, ?_⟩
    intro p
    have hp : A 0 p=false := by
      cases he : A 0 p with
      | false => rfl
      | true => exact False.elim (hex ⟨p,he⟩)
    simpa [hp] using (hs p).symm

theorem lin_self : ∀ a b c : Bool, lin b a b c=rule a b c := by decide +kernel

theorem common_mode_classification (A h : Nat → Nat → Bool)
    (ha : Actual A) (hh : Driven A h) (hw : Common A h)
    (hs : ∀ i, (h 0 i && A 0 i)=h 0 i) :
    ∃ b : Bool, ∀ t i, h t i=(b && A t i) := by
  obtain ⟨b,hb⟩ := initial_phase A h ha hh hw hs
  refine ⟨b, ?_⟩
  intro t
  induction t with
  | zero => exact hb
  | succ t ih =>
    intro i
    rw [hh t i, ih i,ih (i+1),ih (i+2),ha t i]
    cases b
    · simp [lin]
    · simpa using lin_self (A t i) (A t (i+1)) (A t (i+2))

end HalfLine
end Rule30VacuumGaugeResearch
