module
public import ReturnSections
/-! The following counterexample is for an arbitrary cyclically legal
positive boundary word, NOT the actual A^P source. Its exclusion from
the genuine P8 source is proved uniformly in the input prefix length. -/
@[expose] public section
namespace ReachabilityBarrier
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration ReturnActions ReturnSections ReturnSections.State

def good8 : List (List State) :=
  [[A,A,A,A,A,A,A,A],
    [A,A,C,A,C,B,C,B],
    [A,A,C,B,C,C,B,C],
    [A,C,A,C,A,C,A,C],
    [A,C,A,C,B,C,B,A],
    [A,C,B,C,B,A,A,C],
    [A,C,B,C,C,B,C,A],
    [A,C,C,B,A,C,C,B],
    [A,C,C,C,B,C,B,C],
    [B,A,A,C,A,C,B,C],
    [B,A,C,C,B,A,C,C],
    [B,C,A,A,C,B,C,C],
    [B,C,A,C,C,C,B,C],
    [B,C,B,A,A,C,A,C],
    [B,C,B,C,A,C,C,C],
    [B,C,B,C,B,C,B,C],
    [B,C,C,B,C,A,A,C],
    [C,A,A,C,B,C,C,B],
    [C,A,C,A,C,A,C,A],
    [C,A,C,B,C,B,A,A],
    [C,A,C,C,C,B,C,B],
    [C,B,A,A,C,A,C,B],
    [C,B,A,C,C,B,A,C],
    [C,B,C,A,A,C,B,C],
    [C,B,C,A,C,C,C,B],
    [C,B,C,B,A,A,C,A],
    [C,B,C,B,C,A,C,C],
    [C,B,C,B,C,B,C,B],
    [C,B,C,C,B,C,A,A],
    [C,C,B,A,C,C,B,A],
    [C,C,B,C,A,A,C,B],
    [C,C,B,C,B,C,A,C],
    [C,C,C,B,C,B,C,A],
    [C,C,C,C,C,C,C,C]]
def bad : List State := [A,A,A,C,B,C,C,C]
def bits (n : Nat) : Code := n.testBit

theorem good_initial : List.replicate 8 A ∈ good8 := by decide
theorem good_closed_certificate : ∀ i : Fin good8.length,∀ b : Bool,
    parity good8[i]=false → nextWord good8[i] b ∈ good8 := by decide

theorem good_closed (w : List State) (member : w ∈ good8)
    (alive : parity w=false) (b : Bool) : nextWord w b ∈ good8 := by
  obtain ⟨i,hi,eq⟩:=List.getElem_of_mem member
  have h:=good_closed_certificate ⟨i,hi⟩ b
  change parity (good8[i]'hi)=false → nextWord (good8[i]'hi) b ∈ good8 at h
  rw [eq] at h
  exact h alive

theorem fixed_prefix_reachable (n : Nat) (x : Code)
    (fixed : AgreeBelow n (iter 8 x) x) :
    sectionWord (List.replicate 8 A) x n ∈ good8 := by
  revert fixed
  induction n with
  | zero => intro _;exact good_initial
  | succ n ih =>
    intro fixed
    have prior : AgreeBelow n (iter 8 x) x := fun j hj => fixed j (by omega)
    have member:=ih prior
    have alive:=(fixed_prefix_iff 8 (n+1) x).mp fixed n (by omega)
    rw [nextWord_read]
    exact good_closed _ member alive (x n)

theorem bad_not_good : bad ∉ good8 := by decide

/-- All prefix lengths, actual T8, not merely a finite input scan. -/
theorem bad_unreachable (n : Nat) (x : Code)
    (fixed : AgreeBelow n (iter 8 x) x) : returnWord n 8 x≠bad := by
  rw [returnWord_eq]
  intro equal
  have member:=fixed_prefix_reachable n x fixed
  rw [equal] at member
  exact bad_not_good member

theorem bad_root_swaps : parity bad=true := by decide
theorem bad_cyclic_legal :
    (List.range 8).all (fun i => if bad[i]?==some B then
      bad[(i+7)%8]?==some C else true)=true := by decide

-- 010101 and 110101, with the first bit read first, are fixed prefixes
-- of (bad*bad) and have identical return sections. This disproves a
-- generic cyclic-legality induction lemma, but bad_unreachable explains
-- why it does not refute the actual Rule30 return-source conjecture.
theorem bad_square_fixed_left : ∀ i : Fin 6,
    run (bad++bad) (bits 42) i.val=bits 42 i.val := by decide
theorem bad_square_fixed_right : ∀ i : Fin 6,
    run (bad++bad) (bits 43) i.val=bits 43 i.val := by decide
theorem bad_square_merges :
    sectionWord (bad++bad) (bits 42) 6=sectionWord (bad++bad) (bits 43) 6 := by decide
theorem bad_prefixes_distinct : bits 42 0≠bits 43 0 := by decide

end ReachabilityBarrier
