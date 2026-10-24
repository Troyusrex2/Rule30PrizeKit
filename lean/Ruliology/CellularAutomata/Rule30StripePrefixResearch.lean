module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# Whole-prefix restriction used in a failed ranking search

The first stripe deviation of a finite constrained row is at an even depth.
This is a direct consequence of the kit's pivot theorem, not a new period
exclusion. It validates the nonlocal word restriction in the prefix-DFA model;
the numerical ranking searches themselves are not Lean proofs.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30StripePrefixResearch

open Rule30ZeroBoundary

def FirstDefect (L : Nat → Bool) (d : Nat) : Prop :=
  1≤d ∧ (∀ k, 1≤k → k<d → L k=stripe k) ∧ L d≠stripe d

theorem first_defect_white {L : Nat → Bool} {d : Nat} (h : FirstDefect L d) :
    zrow L (d-1) 1=false := by
  have hd : 1≤d := h.1
  have hp := pivot (t:=d-1) (L:=L) (L':=stripe)
    (fun k hk hkd => h.2.1 k hk (by omega)) (by simpa [show d-1+1=d by omega] using h.2.2)
  rw [zrow_stripe] at hp
  change zrow L (d-1) 1≠true at hp
  cases he : zrow L (d-1) 1 <;> simp_all

theorem inX_first_defect_even {L : Nat → Bool} (hX : InX L) {d : Nat}
    (h : FirstDefect L d) : d%2=0 := by
  have hp : 1≤d := h.1
  by_cases hd : d%2=0
  · exact hd
  have ht : 2*((d-1)/2)=d-1 := by omega
  have hb := hX ((d-1)/2)
  rw [ht,first_defect_white h] at hb
  contradiction

theorem finite_first_defect {L : Nat → Bool} (hf : FinSupp L) : ∃ d, FirstDefect L d := by
  have bounded : ∀ n, (∃ k, 1≤k ∧ k≤n ∧ L k≠stripe k) → ∃ d, FirstDefect L d := by
    intro n
    induction n with
    | zero => rintro ⟨k,h1,h2,-⟩; omega
    | succ n ih =>
        intro hex
        by_cases hold : ∃ k, 1≤k ∧ k≤n ∧ L k≠stripe k
        · exact ih hold
        · obtain ⟨k,h1,h2,h3⟩ := hex
          have hk : k=n+1 := by
            apply Classical.byContradiction
            intro hn
            exact hold ⟨k,h1,by omega,h3⟩
          refine ⟨k,h1,fun j hj hjk => ?_,h3⟩
          apply Classical.byContradiction
          intro hne
          exact hold ⟨j,hj,by omega,hne⟩
  obtain ⟨W,hW⟩ := hf
  apply bounded (2*W+1)
  refine ⟨2*W+1,by omega,Nat.le_refl _,?_⟩
  rw [hW _ (by omega)]
  have hs : stripe (2*W+1)=true := by simp [stripe]
  rw [hs]
  decide

theorem finite_inX_even_first_defect {L : Nat → Bool} (hf : FinSupp L) (hX : InX L) :
    ∃ d, FirstDefect L d ∧ d%2=0 := by
  obtain ⟨d,hd⟩ := finite_first_defect hf
  exact ⟨d,hd,inX_first_defect_even hX hd⟩

theorem inX_two_step {L : Nat → Bool} (hX : InX L) : InX (zrow L 2) := by
  intro s
  rw [← zrow_shift,show 2+2*s=2*(s+1) by omega]
  exact hX (s+1)

theorem finite_inX_even_first_defect_two_step {L : Nat → Bool} (hf : FinSupp L) (hX : InX L) :
    (∃ d, FirstDefect L d ∧ d%2=0) ∧
    ∃ d, FirstDefect (zrow L 2) d ∧ d%2=0 := by
  constructor
  · exact finite_inX_even_first_defect hf hX
  · obtain ⟨W,hW⟩ := hf
    exact finite_inX_even_first_defect ⟨W+2,zrow_fin hW 2⟩ (inX_two_step hX)

def Good (L : Nat → Bool) : Prop :=
  FinSupp L ∧ ∃ d, FirstDefect L d ∧ d%2=0

/-- OPEN pathwise ranking specification, not an assertion that one exists.
The lower bound applies on accepted transitions. The infinite-orbit argument
below uses acceptance of the following transition when bounding a later row. -/
def IntegerRanking (V : (Nat → Bool) → Int) : Prop :=
  (∀ L, Good L → Good (zrow L 2) → 0≤V L) ∧
  (∀ L, Good L → Good (zrow L 2) → V (zrow L 2)+1≤V L)

theorem inX_even_shift {L : Nat → Bool} (hX : InX L) (n : Nat) : InX (zrow L (2*n)) := by
  intro s
  rw [← zrow_shift,show 2*n+2*s=2*(n+s) by omega]
  exact hX (n+s)

/-- A successful certificate for this nonlocal specification would prove Q01.
No ranking or certificate satisfying the premise is supplied. -/
theorem Q01_of_integerRanking (V : (Nat → Bool) → Int) (hV : IntegerRanking V) : Q01 := by
  intro L hfin hX
  let rows := fun n => zrow L (2*n)
  have good : ∀ n, Good (rows n) := by
    intro n
    obtain ⟨W,hW⟩ := hfin
    have hf : FinSupp (rows n) := ⟨W+2*n,zrow_fin hW (2*n)⟩
    exact ⟨hf,finite_inX_even_first_defect hf (inX_even_shift hX n)⟩
  have step (n : Nat) : zrow (rows n) 2=rows (n+1) := by
    funext k
    dsimp [rows]
    rw [← zrow_shift,show 2*n+2=2*(n+1) by omega]
  have nextgood (n : Nat) : Good (zrow (rows n) 2) := by
    rw [step]
    exact good (n+1)
  have down (n : Nat) : V (rows (n+1))+1≤V (rows n) := by
    have hn : Good (zrow (rows n) 2) := by rw [step]; exact good (n+1)
    have hh := hV.2 (rows n) (good n) hn
    rwa [step] at hh
  have charge : ∀ n, V (rows n)+(n:Int)≤V (rows 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hd := down n
        simp only [Int.natCast_add,Int.natCast_one]
        omega
  have hlower := hV.1 (rows ((V (rows 0)).toNat+1)) (good _) (nextgood _)
  have hupper := charge ((V (rows 0)).toNat+1)
  have hzero := hV.1 (rows 0) (good 0) (nextgood 0)
  omega

theorem no_eventual_period_two_of_integerRanking
    (V : (Nat → Bool) → Int) (hV : IntegerRanking V) :
    ¬ ∃ T0, ∀ t, T0≤t → Rule30Prize.center (t+2)=Rule30Prize.center t :=
  Rule30ZeroBoundary.no_eventual_period_two (Q01_of_integerRanking V hV)

end Ruliology.CellularAutomata.Rule30StripePrefixResearch
