module
public import Rule30ConservationDescentResearch

/-! All integer local densities satisfying the explicit compact four-step
conservation equation are constant plus a shift coboundary, at every width.
The passage from a Rule30 ranking premise to conservation remains separate. -/
@[expose] public section
namespace Rule30ConservationTrivialityResearch
open Rule30ConservationCornerResearch Rule30ConservationWordResearch
open Rule30ConservationDescentResearch

def Trivial (m : Nat) (h : List Bool → Int) : Prop :=
  ∃ c : Int, ∃ p : List Bool → Int, ∀ xs, xs.length=m →
    h xs=c+p xs.tail-p xs.dropLast

theorem trivial_one (h p : List Bool → Int) (hc : Conserved 1 h p) : Trivial 1 h := by
  have hh:=conserved_one_constant h p hc
  refine ⟨h [false],fun _=>0,?_⟩
  intro xs hx
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    have he : xs=[] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_cons] at hx
      omega
    subst xs
    cases a <;> simp [hh]

/-- No fixed cutoff on m: the local-potential equation has only constant and
telescoping solutions at every positive window length. -/
theorem conserved_trivial : ∀ m : Nat, 0<m → ∀ h p : List Bool → Int,
    Conserved m h p → Trivial m h := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _ h p hc
    by_cases hz : m=0
    · subst m; exact trivial_one h p hc
    have hm : 0<m := by omega
    have hs:=shorter_conserved m (by omega) h p hc
    obtain ⟨c,b,hb⟩:=ih hm (shorter h) (reducedPotential m h p) hs
    refine ⟨c,fun u=>potential h u+b u.dropLast,?_⟩
    intro xs hx
    have hh:=shorten_word m (by omega) h p hc xs hx
    have hl : xs.dropLast.length=m := by rw [List.length_dropLast,hx]; omega
    rw [hb xs.dropLast hl,List.tail_dropLast] at hh
    dsimp only
    omega

def score (h : List Bool → Int) (windows : Nat → List Bool) : Nat → Int
  | 0 => 0
  | n+1 => score h windows n+h (windows n)

theorem trivial_chain (m : Nat) (h : List Bool → Int) (c : Int) (p : List Bool → Int)
    (ht : ∀ xs, xs.length=m → h xs=c+p xs.tail-p xs.dropLast)
    (windows : Nat → List Bool) (hl : ∀ i, (windows i).length=m)
    (ho : ∀ i, (windows i).tail=(windows (i+1)).dropLast) (n : Nat) :
    score h windows n=(n:Int)*c+p (windows n).dropLast-p (windows 0).dropLast := by
  induction n with
  | zero => simp [score]
  | succ n ih =>
    have hh:=ht (windows n) (hl n)
    rw [ho n] at hh
    have hm : ((n+1:Nat):Int)*c=(n:Int)*c+c := by
      change ((n:Int)+1)*c=(n:Int)*c+c
      rw [Int.add_mul,Int.one_mul]
    rw [score,ih,hm]
    omega

/-- Every cyclic rolling-window score from this class is just c times the
cycle length. A boundary potential contributes no bulk conserved charge. -/
theorem conserved_cycle_score (m : Nat) (hm : 0<m) (h p : List Bool → Int)
    (hc : Conserved m h p) : ∃ c : Int, ∀ windows : Nat → List Bool,
    (∀ i, (windows i).length=m) →
    (∀ i, (windows i).tail=(windows (i+1)).dropLast) →
    ∀ n, windows n=windows 0 → score h windows n=(n:Int)*c := by
  obtain ⟨c,b,hb⟩:=conserved_trivial m hm h p hc
  refine ⟨c,?_⟩
  intro windows hl ho n he
  have hh:=trivial_chain m h c b hb windows hl ho n
  rw [he] at hh
  omega

end Rule30ConservationTrivialityResearch
