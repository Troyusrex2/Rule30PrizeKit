from pathlib import Path
from collections import deque
import json
R=Path(__file__).resolve().parent
def section(w,b):
    out=[]
    for q in reversed(w):out.append(2 if b else (1 if q==2 else 0));b^=q!=0
    return tuple(reversed(out))
root=(0,)*8;seen={root};queue=deque([root])
while queue:
    w=queue.popleft()
    if sum(q!=0 for q in w)%2:continue
    for b in [0,1]:
        v=section(w,b)
        if v not in seen:seen.add(v);queue.append(v)
bad=(0,0,0,2,1,2,2,2);assert bad not in seen
names=['A','B','C']
words=',\n    '.join('['+','.join(names[q] for q in w)+']' for w in sorted(seen))
source='''module
public import ReturnSections
/-! The following counterexample is for an arbitrary cyclically legal
positive boundary word, NOT the actual A^P source. Its exclusion from
the genuine P8 source is proved uniformly in the input prefix length. -/
@[expose] public section
namespace ReachabilityBarrier
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration ReturnActions ReturnSections ReturnSections.State

def good8 : List (List State) :=
  ['''+words+''']
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
'''
(R/'ReachabilityBarrier.lean').write_text(source,encoding='utf-8')
(R/'REACHABILITY.json').write_text(json.dumps(dict(period=8,states=len(seen),bad=list(bad),
    bad_reachable=False,method='All fixed-input graph vertices from A8; finite exact closure. Lean supplies all-depth induction.',
    bad_square_prefixes=[42,43],prefix_length=6),indent=2)+'\n')
print(json.dumps(dict(states=len(seen),bad_reachable=False)))
