namespace Ordinary
open _root_.Ruliology.CellularAutomata.Rule30Jen (cell)

def read (U : Nat) (h : Nat → Int → Bool) (t j : Nat) : Bool :=
  h t ((U : Int)+t-j)
def readB (U V t j : Nat) : Bool := cell (V+t) ((U : Int)+t-j)

theorem read_evolution (U V : Nat) (hUV : V ≤ U) (h : Nat → Int → Bool)
    (hh : RightWedge.Mode U V h) (hi : ∀ p, (U : Int) < p → h 0 p=false) :
    Evolution (canonical U) (readB U V) (read U h) := by
  intro t j
  cases j with
  | zero =>
    change h (t+1) ((U : Int)+(t+1)-0)=h t ((U : Int)+t-0)
    simp only [Int.sub_zero]
    have h1 := RightWedge.mode_right_edge U V h hh hi (t+1)
    have h0 := RightWedge.mode_right_edge U V h hh hi t
    simpa only [Int.natCast_add,Int.natCast_one] using h1.trans h0.symm
  | succ j =>
    cases j with
    | zero =>
      have hm := hh t ((U : Int)+t)
      unfold RightWedge.dStep at hm
      have hb := Rule30Diagonals.cell_eq_false_of_gt (V+t) ((U : Int)+t+1) (by omega)
      have hz := RightWedge.mode_right_white U V h hh hi t ((U : Int)+t+1) (by omega)
      rw [hb,hz] at hm
      change h (t+1) ((U : Int)+(t+1)-1)=_
      rw [show (U : Int)+(t+1)-1=(U : Int)+t by omega]
      simpa [read,step] using hm
    | succ j =>
      let p : Int := (U : Int)+(t+1)-(j+2)
      have hl : p-1=(U : Int)+t-(j+2) := by dsimp [p]; omega
      have hc : p=(U : Int)+t-(j+1) := by dsimp [p]; omega
      have hr : p+1=(U : Int)+t-j := by dsimp [p]; omega
      have hm := hh t p
      unfold RightWedge.dStep at hm
      rw [hl,hr,hc] at hm
      change h (t+1) p=step (canonical U t) (readB U V t) (read U h t) (j+2)
      rw [hc]
      simpa [read,readB,step,canonical,R,Int.natCast_add] using hm

theorem read_nonzero (U : Nat) (h : Nat → Int → Bool)
    (hi : ∀ p, (U : Int) < p → h 0 p=false) (hne : ∃ p, h 0 p=true) :
    ∃ j, read U h 0 j=true := by
  obtain ⟨p,hp⟩ := hne
  have hpU : p ≤ U := by
    apply Classical.byContradiction
    intro hn
    rw [hi p (by omega)] at hp
    cases hp
  refine ⟨((U : Int)-p).toNat,?_⟩
  have he : (U : Int)+0-(((U : Int)-p).toNat : Int)=p := by omega
  simpa only [read,Int.natCast_zero,he] using hp

/-- Ordinary coordinates: every nonzero initially upper-bounded D field
visits arbitrarily far behind the older moving right front, after every time.
No common-gauge or initial subset hypothesis is used. -/
theorem arbitrarily_far_behind_front (U V : Nat) (hUV : V ≤ U)
    (h : Nat → Int → Bool) (hh : RightWedge.Mode U V h)
    (hi : ∀ p, (U : Int) < p → h 0 p=false) (hne : ∃ p, h 0 p=true)
    (T L : Nat) :
    ∃ t, T ≤ t ∧ ∃ p : Int, p ≤ (U : Int)+t-L ∧ h t p=true := by
  obtain ⟨t,ht,j,hj,hblack⟩ := arbitrarily_deep_after_any_time U (readB U V) (read U h)
    (read_evolution U V hUV h hh hi) (read_nonzero U h hi hne) T L
  exact ⟨t,ht,(U : Int)+t-j,by omega,hblack⟩

end Ordinary
