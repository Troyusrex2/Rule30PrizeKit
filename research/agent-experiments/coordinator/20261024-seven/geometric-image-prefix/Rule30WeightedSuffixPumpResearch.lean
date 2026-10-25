import Rule30WeightedWordPumpResearch
import Mathlib.Tactic.Ring

/-! A fixed suffix can be absorbed into a constant geometric score gauge.
This extends the absorbing-state pump obstruction to words whose finite
moving front contributes a nonempty suffix. -/
namespace Rule30WeightedSuffixPumpResearch
open Rule30WeightedWordPumpResearch

def shiftedCost (C : Nat → Bool → Int) (lam : Nat) (Z : Int) : Nat → Bool → Int :=
  fun p a=>C p a+((lam:Int)-1)*Z

theorem score_shifted (T : Nat → Bool → Nat) (C : Nat → Bool → Int)
    (lam : Nat) (Z : Int) (w : List Bool) (p : Nat) :
    score T (shiftedCost C lam Z) lam p w=
      score T C lam p w+(scale lam w.length-1)*Z := by
  induction w generalizing p with
  | nil => simp [score,scale]
  | cons a w ih =>
    simp only [score,shiftedCost,ih,List.length_cons]
    rw [show scale lam (w.length+1)=(lam:Int)*scale lam w.length from rfl]
    ring

theorem gauge_suffix (T : Nat → Bool → Nat) (C : Nat → Bool → Int)
    (lam p s : Nat) (w z : List Bool) (hw : run T p w=s) :
    score T (shiftedCost C lam (score T C lam s z)) lam p w+score T C lam s z=
      score T C lam p (w++z) := by
  rw [score_shifted,score_append,hw]
  ring

theorem suffix_loop_nonnegative (T : Nat → Bool → Nat) (C : Nat → Bool → Int)
    {lam : Nat} (hlam : 1≤lam) (p s : Nat) (w v z : List Bool)
    (hw : run T p w=s) (hs : ∀ a,T s a=s)
    (hb : ∃ B:Int,∀ n,B≤score T C lam p (w++copies v n++z)) :
    0≤score T C lam s v+(scale lam v.length-1)*score T C lam s z := by
  let D:=shiftedCost C lam (score T C lam s z)
  have hbD : ∃ B:Int,∀ n,B≤score T D lam p (w++copies v n) := by
    obtain ⟨B,hB⟩:=hb
    refine ⟨B-score T C lam s z,fun n=>?_⟩
    have h:=hB n
    have he:=gauge_suffix T C lam p s (w++copies v n) z (run_pumped T p s w v hw hs n)
    change score T D lam p (w++copies v n)+score T C lam s z=
      score T C lam p (w++copies v n++z) at he
    omega
  have hno:=no_absorbing_tail_decrease T D hlam p s w v hw hs hbD
  have hn : 0≤score T D lam s v := by
    apply Classical.byContradiction
    intro hneg
    have hle : score T D lam s v≤-1 := by omega
    have hp:=scale_ge_one hlam w.length
    have hm:=Int.mul_le_mul_of_nonneg_left hle (show 0≤scale lam w.length by omega)
    simp only [Int.mul_neg_one] at hm
    apply hno
    rw [score_append,hw]
    omega
  simpa only [D,score_shifted] using hn

end Rule30WeightedSuffixPumpResearch
