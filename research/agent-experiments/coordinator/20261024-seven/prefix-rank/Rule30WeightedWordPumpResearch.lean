import Ruliology.CellularAutomata.Rule30Prize

/-! A bounded-below signed geometric reader cannot strictly decrease on a
word extension after it has reached an absorbing state. The repeated tail
would otherwise drive the energy to minus infinity. This is an obstruction
for a precisely specified rank family, not a Rule 30 nonperiodicity proof. -/

namespace Rule30WeightedWordPumpResearch

def run (T : Nat → Bool → Nat) : Nat → List Bool → Nat
  | p,[] => p
  | p,a::w => run T (T p a) w

def scale (lam : Nat) : Nat → Int
  | 0 => 1
  | n+1 => (lam:Int)*scale lam n

def score (T : Nat → Bool → Nat) (C : Nat → Bool → Int) (lam : Nat) :
    Nat → List Bool → Int
  | _,[] => 0
  | p,a::w => C p a+(lam:Int)*score T C lam (T p a) w

def copies (v : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => copies v n++v

theorem run_append (T : Nat → Bool → Nat) (w v : List Bool) (p : Nat) :
    run T p (w++v) = run T (run T p w) v := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih => simpa only [List.cons_append,run] using ih (T p a)

theorem score_append (T : Nat → Bool → Nat) (C : Nat → Bool → Int) (lam : Nat)
    (w v : List Bool) (p : Nat) :
    score T C lam p (w++v) = score T C lam p w+
      scale lam w.length*score T C lam (run T p w) v := by
  induction w generalizing p with
  | nil => simp [score,run,scale]
  | cons a w ih =>
    simp only [List.cons_append,score,run,List.length_cons,scale,ih,
      Int.mul_add,Int.mul_assoc,Int.add_assoc]

theorem scale_ge_one {lam : Nat} (hlam : 1≤lam) (n : Nat) : 1≤scale lam n := by
  induction n with
  | zero => exact Int.le_refl 1
  | succ n ih =>
    have h := Int.mul_le_mul_of_nonneg_left ih (show 0≤(lam:Int) by omega)
    simp only [Int.mul_one] at h
    rw [scale]
    omega

theorem run_absorbing (T : Nat → Bool → Nat) (s : Nat) (hs : ∀ a,T s a=s)
    (w : List Bool) : run T s w=s := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [run,hs] using ih

theorem run_pumped (T : Nat → Bool → Nat) (p s : Nat) (w v : List Bool)
    (hw : run T p w=s) (hs : ∀ a,T s a=s) (n : Nat) :
    run T p (w++copies v n)=s := by
  rw [run_append,hw]
  exact run_absorbing T s hs _

theorem no_bounded_strict_descent (E : Nat → Int) (B : Int)
    (hb : ∀ n,B≤E n) (hd : ∀ n,E (n+1)≤E n-1) : False := by
  have h : ∀ n,E n≤E 0-(n:Int) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have hh:=hd n; omega
  let n := (E 0-B).toNat+1
  have hn : E 0-B<(n:Int) := by dsimp only [n]; omega
  have h1:=hb n
  have h2:=h n
  omega

theorem no_absorbing_tail_decrease (T : Nat → Bool → Nat) (C : Nat → Bool → Int)
    {lam : Nat} (hlam : 1≤lam) (p s : Nat) (w v : List Bool)
    (hw : run T p w=s) (hs : ∀ a,T s a=s)
    (hb : ∃ B:Int,∀ n,B≤score T C lam p (w++copies v n)) :
    ¬ score T C lam p (w++v)<score T C lam p w := by
  intro hdec
  have hsneg : score T C lam s v≤-1 := by
    rw [score_append,hw] at hdec
    have hp:=scale_ge_one hlam w.length
    apply Classical.byContradiction
    intro hn
    have hc : 0≤score T C lam s v := by omega
    have hm:=Int.mul_nonneg (show 0≤scale lam w.length by omega) hc
    omega
  obtain ⟨B,hB⟩:=hb
  apply no_bounded_strict_descent (fun n=>score T C lam p (w++copies v n)) B hB
  intro n
  rw [copies,←List.append_assoc,score_append,run_pumped T p s w v hw hs n]
  have hp:=scale_ge_one hlam (w++copies v n).length
  have hm:=Int.mul_le_mul_of_nonneg_left hsneg
    (show 0≤scale lam (w++copies v n).length by omega)
  simp only [Int.mul_neg_one] at hm
  omega

end Rule30WeightedWordPumpResearch
