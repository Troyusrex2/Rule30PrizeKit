import Rule30GoldenCompactBudgetResearch

/-! Algebraic obstruction to prefix-monotone ranks. The two actual examples
are independently physically reconstructed by the companion Python controls.
This module checks the word extension and order contradiction, not the full
Python-to-official-evolution bridge. -/
namespace Rule30PrefixMonotoneRankObstructionResearch
def shortWord : List Nat := [3,2,1,0,2,3,2,3,0,3,0,0,2,1,2,1]

def middleWord : List Nat := [2,1,2,1,0,0,2,1,3,0,2,1,1,1,3,2,1,0]

def longWord : List Nat := [3,2,1,0,2,3,2,3,0,3,0,0,2,1,2,1,2,1,0,0]

def extension : List Nat := [2,1,0,0]

theorem long_eq : longWord=shortWord++extension := by rfl

theorem no_prefix_monotone_rank (E : Nat -> List Nat -> Int)
    (hext : forall p xs tail, E p xs <= E p (xs++tail))
    (h0 : E 21 middleWord+1 <= E 42 shortWord)
    (h1 : E 42 longWord <= E 21 middleWord) : False := by
  have hp := hext 42 shortWord extension
  rw [<-long_eq] at hp
  omega

end Rule30PrefixMonotoneRankObstructionResearch
