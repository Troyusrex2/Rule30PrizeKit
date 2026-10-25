module

public import Rule30VacuumGaugeResearch
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
Apply vacuum-gauge rigidity to the exact exterior of a younger canonical row.
All statements retain the actual single-seed ages. The center and the canonical
left edge are outside this right exterior; no prize or observer proof is claimed.
-/

@[expose] public section
namespace Rule30RightWedgeResearch
open Ruliology.CellularAutomata
open Rule30Jen (cell rule)
open Rule30VacuumGaugeResearch

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

end Rule30RightWedgeResearch
