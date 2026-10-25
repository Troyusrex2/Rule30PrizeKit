module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
All-time common-gauge rigidity with a zero background. The auxiliary field
is not assumed to be a physical Rule30 history. This adapts the catalog's
XOR-rigidity gap argument, keeping an asymmetric black right endpoint.
The right-wedge section applies it uniformly to every actual canonical age
pair U>V. Beyond the younger row's right front, any supported common field
equals its initial older-right-edge bit times the older canonical row.
The finite-horizon version has a distance-dependent bound. The overlap
containing the center and the left edge remains unresolved.
Proof and formalization: Troy Lowry with OpenAI Codex.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30CommonGauge
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

namespace RightWedge
open _root_.Ruliology.CellularAutomata.Rule30Jen (cell)

def delta (U V t : Nat) (p : Int) := xor (cell (U+t) p) (cell (V+t) p)
def dStep (U V : Nat) (h : Nat → Int → Bool) (t : Nat) (p : Int) :=
  xor (xor (h t (p-1)) ((!cell (V+t) (p+1)) && h t p))
    ((!cell (U+t) p) && h t (p+1))
def Mode (U V : Nat) (h : Nat → Int → Bool) : Prop :=
  ∀ t p, h (t+1) p=dStep U V h t p
def Common (U V : Nat) (h : Nat → Int → Bool) : Prop :=
  ∀ t p, Good (delta U V t p) (h t p) (delta U V t (p+1)) (h t (p+1))
def CommonThrough (U V : Nat) (h : Nat → Int → Bool) (N : Nat) : Prop :=
  ∀ t, t ≤ N → ∀ p, Good (delta U V t p) (h t p) (delta U V t (p+1)) (h t (p+1))

def site (V t i : Nat) : Int := (V : Int)+1+t+i
def rightA (U V : Nat) (t i : Nat) := cell (U+t) (site V t i)
def rightH (V : Nat) (h : Nat → Int → Bool) (t i : Nat) := h t (site V t i)

theorem site_left (V t i : Nat) : site V (t+1) i-1=site V t i := by
  simp only [site]; omega
theorem site_center (V t i : Nat) : site V (t+1) i=site V t (i+1) := by
  simp only [site]; omega
theorem site_right (V t i : Nat) : site V (t+1) i+1=site V t (i+2) := by
  simp only [site]; omega
theorem site_neighbor (V t i : Nat) : site V t i+1=site V t (i+1) := by
  simp only [site]; omega
theorem younger_white (V t i : Nat) : cell (V+t) (site V t i)=false := by
  apply Rule30Diagonals.cell_eq_false_of_gt
  simp only [site]; omega

theorem right_cut_actual (U V : Nat) : HalfLine.Actual (rightA U V) := by
  intro t i
  change cell (U+(t+1)) (site V (t+1) i)=_
  rw [show U+(t+1)=(U+t)+1 by omega]
  change rule (cell (U+t) (site V (t+1) i-1)) (cell (U+t) (site V (t+1) i))
    (cell (U+t) (site V (t+1) i+1)) = _
  rw [site_left, site_right, site_center]
  rfl

theorem right_cut_driven (U V : Nat) (h : Nat → Int → Bool) (hh : Mode U V h) :
    HalfLine.Driven (rightA U V) (rightH V h) := by
  intro t i
  have hm := hh t (site V (t+1) i)
  unfold dStep at hm
  rw [site_left,site_right,site_center,younger_white] at hm
  simpa only [rightA,rightH,lin,site_center,Bool.not_false,Bool.true_and] using hm

theorem right_cut_common (U V : Nat) (h : Nat → Int → Bool) (hw : Common U V h) :
    HalfLine.Common (rightA U V) (rightH V h) := by
  intro t i
  have hm := hw t (site V t i)
  unfold delta at hm
  rw [site_neighbor,younger_white,younger_white] at hm
  simpa only [rightA,rightH,Bool.xor_false] using hm

theorem right_cut_common_through (U V : Nat) (h : Nat → Int → Bool) (N : Nat)
    (hw : CommonThrough U V h N) :
    HalfLine.CommonThrough (rightA U V) (rightH V h) N := by
  intro t ht i
  have hm := hw t ht (site V t i)
  unfold delta at hm
  rw [site_neighbor,younger_white,younger_white] at hm
  simpa only [rightA,rightH,Bool.xor_false] using hm

theorem mode_right_white (U V : Nat) (h : Nat → Int → Bool) (hh : Mode U V h)
    (hi : ∀ p, (U : Int) < p → h 0 p=false) :
    ∀ (t : Nat) (p : Int), (U : Int)+t < p → h t p=false := by
  intro t
  induction t with
  | zero => intro p hp; exact hi p (by omega)
  | succ t ih =>
    intro p hp
    rw [hh t p]
    simp only [dStep,ih (p-1) (by omega),ih p (by omega),ih (p+1) (by omega)]
    simp

theorem mode_right_edge (U V : Nat) (h : Nat → Int → Bool) (hh : Mode U V h)
    (hi : ∀ p, (U : Int) < p → h 0 p=false) :
    ∀ t, h t ((U : Int)+t)=h 0 U := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hh]
    have e : (U : Int)+(t+1 : Nat)-1=(U : Int)+t := by omega
    have hw0 := mode_right_white U V h hh hi t ((U : Int)+(t+1 : Nat)) (by omega)
    have hw1 := mode_right_white U V h hh hi t ((U : Int)+(t+1 : Nat)+1) (by omega)
    rw [dStep,e,hw0,hw1]
    simpa using ih

/-- A finite, distance-dependent common-gauge horizon suffices in the right
exterior. It does not give a fixed horizon independent of the ages. -/
theorem right_wedge_phase_through (U V : Nat) (hUV : V<U) (h : Nat → Int → Bool)
    (hh : Mode U V h) (N : Nat) (hw : CommonThrough U V h N)
    (hi : ∀ p, (U : Int) < p → h 0 p=false)
    (t : Nat) (p : Int) (hp : (V : Int)+t < p)
    (ht : t+((U : Int)+t-p).toNat/2 ≤ N) :
    h t p=(h 0 U && cell (U+t) p) := by
  by_cases hout : (U : Int)+t < p
  · rw [mode_right_white U V h hh hi t p hout,
      Rule30Diagonals.cell_eq_false_of_gt (U+t) p (by omega)]
    simp
  · let i := (p-((V : Int)+1+t)).toNat
    let q := U-V-1
    have hiq : i ≤ q := by dsimp [i,q]; omega
    have hsi : site V t i=p := by dsimp [site,i]; omega
    have hsq : site V t q=(U : Int)+t := by dsimp [site,q]; omega
    have heq : i+(q-i)=q := Nat.add_sub_of_le hiq
    have hd : q-i=((U : Int)+t-p).toNat := by dsimp [q,i]; omega
    have hblack : rightA U V t (i+(q-i))=true := by
      rw [heq]
      change cell (U+t) (site V t q)=true
      rw [hsq]
      simpa only [Rule30Diagonals.R,Int.natCast_zero,Int.sub_zero,Int.natCast_add] using
        Rule30Diagonals.R_zero (U+t)
    have hg := HalfLine.distant_good_right_black_through (rightA U V) (rightH V h)
      (right_cut_actual U V) (right_cut_driven U V h hh) N
      (right_cut_common_through U V h N hw) (q-i) t i (by omega) hblack
    rw [heq] at hg
    have haedge : cell (U+t) ((U : Int)+t)=true := by
      simpa only [Rule30Diagonals.R,Int.natCast_zero,Int.sub_zero,Int.natCast_add] using
        Rule30Diagonals.R_zero (U+t)
    simpa [rightA,rightH,hsi,hsq,Good,haedge,mode_right_edge U V h hh hi t,
      Bool.and_comm] using hg.symm

/-- All-time consequence for every actual canonical age pair U>V. -/
theorem right_wedge_phase (U V : Nat) (hUV : V<U) (h : Nat → Int → Bool)
    (hh : Mode U V h) (hw : Common U V h)
    (hi : ∀ p, (U : Int) < p → h 0 p=false) :
    ∀ (t : Nat) (p : Int), (V : Int)+t < p → h t p=(h 0 U && cell (U+t) p) := by
  intro t p hp
  exact right_wedge_phase_through U V hUV h hh (t+((U : Int)+t-p).toNat/2)
    (fun s _ x => hw s x) hi t p hp (by omega)

theorem subset_right_white (U V : Nat) (hUV : V<U) (h : Nat → Int → Bool)
    (hs : ∀ p, (h 0 p && delta U V 0 p)=h 0 p) :
    ∀ p, (U : Int) < p → h 0 p=false := by
  intro p hp
  have ha := Rule30Diagonals.cell_eq_false_of_gt U p hp
  have hb := Rule30Diagonals.cell_eq_false_of_gt V p (by omega)
  have h := hs p
  simpa [delta,ha,hb] using h.symm

theorem right_wedge_phase_subset (U V : Nat) (hUV : V<U) (h : Nat → Int → Bool)
    (hh : Mode U V h) (hw : Common U V h)
    (hs : ∀ p, (h 0 p && delta U V 0 p)=h 0 p) :
    ∀ (t : Nat) (p : Int), (V : Int)+t < p → h t p=(h 0 U && cell (U+t) p) :=
  right_wedge_phase U V hUV h hh hw (subset_right_white U V hUV h hs)

end RightWedge
end Ruliology.CellularAutomata.Rule30CommonGauge
