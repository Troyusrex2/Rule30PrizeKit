"""Generalize the existing verified range descent; never edit its source."""
from pathlib import Path
import hashlib,json,re,shutil
root=Path(__file__).resolve().parent
source=Path(r'D:\MWB\Rule30\overnight-20261024\research\agent-experiments\coordinator\20261025-conservation-catalog\Rule30LocalConservation.lean')
original=source.read_text(encoding='utf-8')
body=original[original.index('theorem getD_append_prefix'):original.index('\ndef score')]
body=body.replace('List Bool','List (Cell ι)').replace(' : Bool',' : Cell ι')
body=re.sub(r'\bInt\b','G',body)
body=re.sub(r'\bfalse\b','zeroCell',body)
body=re.sub(r'\bxor\b','bxor',body)
def section(start,end,replacement):
    global body
    i=body.index(start);j=body.index(end,i)
    body=body[:i]+replacement+'\n\n'+body[j:]
section('theorem image_preimage','theorem preimage_suffix',r'''theorem image_preimage (xs : List (Cell ι)) : image (preimage xs)=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    have hp : 8≤(preimage xs).length := by rw [preimage_length]; omega
    have hq : q (bxor b (q zeroCell (preimage xs))) (preimage xs)=b := by
      rw [q_left]
      exact bxor_cancel _ _
    simp only [preimage,image,ite_eq_left hp,hq,ih]''')
section('theorem image_white_suffix','/-- Two freely chosen',r'''theorem image_nine (a b : Cell ι) :
    image (a::(List.replicate 7 zeroCell++[b]))=[bxor a b] := by
  change [q9 a zeroCell zeroCell zeroCell zeroCell zeroCell zeroCell zeroCell b]=[bxor a b]
  rw [q9_right_zero]

theorem image_white_suffix (u : List (Cell ι)) (b : Cell ι) :
    image (u++List.replicate 8 zeroCell++[b])=
      image (u++List.replicate 8 zeroCell)++[b] := by
  induction u with
  | nil =>
    change image (zeroCell::(List.replicate 7 zeroCell++[b]))=[b]
    rw [image_nine,bxor_zero_left]
  | cons a u ih =>
    have hx : 8≤(u++List.replicate 8 zeroCell).length := by simp
    have hy : 8≤((u++List.replicate 8 zeroCell)++[b]).length := by simp
    simp only [List.cons_append,image,ite_eq_left hx,ite_eq_left hy,q_append a b _ hx,ih]''')
section('theorem conserved_rectangle','def potential',r'''theorem conserved_rectangle (ys : List (Cell ι)) (h p : List (Cell ι) → G)
    (hc : Conserved (ys.length+2) h p) (a b : Cell ι) :
    h (a::(ys++[b]))=h (a::(ys++[zeroCell]))+
      h (zeroCell::(ys++[b]))-h (zeroCell::(ys++[zeroCell])) := by
  let q0 := q zeroCell (preimage ys)
  have hl : (preimage ys).length=ys.length+2+6 := by rw [preimage_length]
  have h00 := hc (preimage ys) hl q0 zeroCell
  have h01 := hc (preimage ys) hl q0 b
  have h10 := hc (preimage ys) hl (bxor a q0) zeroCell
  have h11 := hc (preimage ys) hl (bxor a q0) b
  rw [image_rectangle] at h00 h01 h10 h11
  change h (bxor q0 q0::(ys++[zeroCell]))=_ at h00
  change h (bxor q0 q0::(ys++[b]))=_ at h01
  change h (bxor (bxor a q0) q0::(ys++[zeroCell]))=_ at h10
  change h (bxor (bxor a q0) q0::(ys++[b]))=_ at h11
  simp only [bxor_self,bxor_cancel] at h00 h01 h10 h11
  rw [h11,h10,h01,h00]
  abel''')
section('theorem shorten_density','end Corner',r'''theorem shorten_density (ys : List (Cell ι)) (h p : List (Cell ι) → G)
    (hc : Conserved (ys.length+2) h p) (a b : Cell ι) :
    h (a::(ys++[b]))=shorter h (a::ys)+
      potential h (ys++[b])-potential h (a::ys) := by
  have hr := conserved_rectangle ys h p hc a b
  unfold shorter potential
  simp only [List.cons_append,List.tail_cons]
  apply sub_eq_zero.mp
  convert (sub_eq_zero.mpr hr) using 1 <;> abel''')
section('theorem conserved_one_constant','end Word',r'''theorem conserved_one_constant (h p : List (Cell ι) → G) (hc : Conserved 1 h p)
    (a : Cell ι) : h [zeroCell]=h [a] := by
  have old := hc (List.replicate 7 a) (by simp) a a
  have himg : image (a::(List.replicate 7 a++[a]))=[zeroCell] := by
    change [q9 a a a a a a a a a]=[zeroCell]
    rw [q9_diag]
  rw [himg] at old
  change h [zeroCell]=h [a]+p (List.replicate 8 a)-p (List.replicate 8 a) at old
  simpa using old''')
needle='  unfold transport\n  omega'
assert needle in body
body=body.replace(needle,'  unfold transport\n  apply sub_eq_zero.mp\n  convert (sub_eq_zero.mpr old) using 1 <;> abel',1)
section('theorem transport_last_independent','def reducedPotential',r'''theorem transport_last_independent (m : Nat) (hm : 1≤m) (h p : List (Cell ι) → G)
    (hc : Conserved (m+1) h p) (xs : List (Cell ι)) (hx : xs.length=m+7) (b : Cell ι) :
    transport m h p (xs++[zeroCell])=transport m h p (xs++[b]) := by
  have hl : (zeroCell::xs).length=m+8 := by simp [hx,Nat.add_assoc]
  have h0 := transport_identity m hm h p hc (zeroCell::xs) hl zeroCell
  have h1 := transport_identity m hm h p hc (zeroCell::xs) hl b
  simp only [List.tail_cons] at h0 h1
  exact sub_right_inj.mp (h0.symm.trans h1)''')
section('theorem transport_reduced','/-- The explicit shorter',r'''theorem transport_reduced (m : Nat) (hm : 1≤m) (h p : List (Cell ι) → G)
    (hc : Conserved (m+1) h p) (xs : List (Cell ι)) (hx : xs.length=m+8) :
    transport m h p xs=reducedPotential m h p xs.dropLast := by
  have hn : xs≠[] := by intro he; simp [he] at hx
  let b:=xs.getLast hn
  have he : xs.dropLast++[b]=xs := List.dropLast_concat_getLast hn
  have hl : xs.dropLast.length=m+7 := by rw [List.length_dropLast,hx]; omega
  have hi := transport_last_independent m hm h p hc xs.dropLast hl b
  unfold reducedPotential
  rw [←he]
  simp only [List.dropLast_concat]
  exact hi.symm''')
section('theorem trivial_one','/-- No fixed cutoff',r'''theorem trivial_one (h p : List (Cell ι) → G) (hc : Conserved 1 h p) : Trivial 1 h := by
  refine ⟨h [zeroCell],fun _=>0,?_⟩
  intro xs hx
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    have he : xs=[] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_cons] at hx
      omega
    subst xs
    simpa using (conserved_one_constant h p hc a).symm''')
needle='    dsimp only\n    omega';assert needle in body
body=body.replace(needle,'    dsimp only\n    apply sub_eq_zero.mp\n    convert (sub_eq_zero.mpr hh) using 1 <;> abel',1)
prefix=r'''module

public import Mathlib.Tactic
public import Ruliology.CellularAutomata.Rule30Prize

/-!
Uniform range descent for ANY coordinatewise product of Rule30 and densities
in ANY additive commutative group. This includes paired F2 charges. It is a
four-step local-current classification, not a solution of a prize problem.
Adapted from the earlier integer scalar proof; no literature novelty claimed.
-/

@[expose] public section
universe u v
namespace Rule30ProductConservationResearch
variable {ι : Type u} {G : Type v} [AddCommGroup G]
abbrev Cell (ι : Type u) := ι → Bool
def zeroCell : Cell ι := fun _ => false
def bxor (a b : Cell ι) : Cell ι := fun i => xor (a i) (b i)
theorem bxor_cancel (a b : Cell ι) : bxor (bxor a b) b=a := by
  funext i
  change xor (xor (a i) (b i)) (b i)=a i
  cases a i <;> cases b i <;> rfl
theorem bxor_self (a : Cell ι) : bxor a a=zeroCell := by
  funext i
  change xor (a i) (a i)=false
  cases a i <;> rfl
theorem bxor_zero_left (a : Cell ι) : bxor zeroCell a=a := by
  funext i
  change xor false (a i)=a i
  cases a i <;> rfl

namespace Corner
def rule (a b c : Cell ι) : Cell ι := fun i =>
  Ruliology.CellularAutomata.Rule30Jen.rule (a i) (b i) (c i)
def shrink : List (Cell ι) → List (Cell ι)
  | a::b::c::xs => rule a b c :: shrink (b::c::xs)
  | _ => []
def four (xs : List (Cell ι)) : List (Cell ι) := shrink (shrink (shrink (shrink xs)))
def scalarShrink : List Bool → List Bool
  | a::b::c::xs => Ruliology.CellularAutomata.Rule30Jen.rule a b c :: scalarShrink (b::c::xs)
  | _ => []
def scalarQ9 (a b c d e f g h i : Bool) : Bool :=
  (scalarShrink (scalarShrink (scalarShrink (scalarShrink [a,b,c,d,e,f,g,h,i])))).headD false
theorem scalar_left : ∀ a b c d e f g h i : Bool,
    scalarQ9 a b c d e f g h i=xor a (scalarQ9 false b c d e f g h i) := by decide +kernel
theorem scalar_right : ∀ a b : Bool,
    scalarQ9 a false false false false false false false b=xor a b := by decide +kernel
theorem scalar_diag : ∀ a : Bool, scalarQ9 a a a a a a a a a=false := by decide +kernel
def q9 (a b c d e f g h i : Cell ι) : Cell ι :=
  (four [a,b,c,d,e,f,g,h,i]).headD zeroCell
def q (a : Cell ι) (xs : List (Cell ι)) : Cell ι :=
  q9 a (xs.getD 0 zeroCell) (xs.getD 1 zeroCell) (xs.getD 2 zeroCell) (xs.getD 3 zeroCell)
    (xs.getD 4 zeroCell) (xs.getD 5 zeroCell) (xs.getD 6 zeroCell) (xs.getD 7 zeroCell)
theorem q9_left : ∀ a b c d e f g h i : Cell ι,
    q9 a b c d e f g h i=bxor a (q9 zeroCell b c d e f g h i) := by
  intro a b c d e f g h i
  funext j
  change scalarQ9 (a j) (b j) (c j) (d j) (e j) (f j) (g j) (h j) (i j)=
    xor (a j) (scalarQ9 false (b j) (c j) (d j) (e j) (f j) (g j) (h j) (i j))
  exact scalar_left _ _ _ _ _ _ _ _ _
theorem q_left (a : Cell ι) (xs : List (Cell ι)) : q a xs=bxor a (q zeroCell xs) :=
  q9_left a _ _ _ _ _ _ _ _
theorem q9_right_zero (a b : Cell ι) :
    q9 a zeroCell zeroCell zeroCell zeroCell zeroCell zeroCell zeroCell b=bxor a b := by
  funext j
  change scalarQ9 (a j) false false false false false false false (b j)=xor (a j) (b j)
  exact scalar_right _ _
theorem q9_diag (a : Cell ι) : q9 a a a a a a a a a=zeroCell := by
  funext j
  change scalarQ9 (a j) (a j) (a j) (a j) (a j) (a j) (a j) (a j) (a j)=false
  exact scalar_diag _

'''
suffix=r'''
end Triviality

/-- All widths, any family of Rule30 coordinates, and any abelian coefficient
group. The assumption is the exact four-step compact local-current equation. -/
theorem all_widths (m : Nat) (hm : 0<m) (h p : List (Cell ι) → G)
    (hc : Corner.Conserved m h p) :
    ∃ c : G, ∃ b : List (Cell ι) → G, ∀ xs, xs.length=m →
      h xs=c+b xs.tail-b xs.dropLast :=
  Triviality.conserved_trivial m hm h p hc

/-- The mixed-pair mod-two specialization; no finite width cutoff. -/
theorem paired_F2 (m : Nat) (hm : 0<m)
    (h p : List (Cell (Fin 2)) → ZMod 2) (hc : Corner.Conserved m h p) :
    ∃ c : ZMod 2, ∃ b : List (Cell (Fin 2)) → ZMod 2, ∀ xs, xs.length=m →
      h xs=c+b xs.tail-b xs.dropLast := all_widths m hm h p hc

end Rule30ProductConservationResearch
'''
text=prefix+body+suffix
assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|skipKernel|decide\s*\+native',text)
(root/'Rule30ProductConservationResearch.lean').write_text(text,encoding='utf-8',newline='\n')
oldrunner=(root.parent/'observer-algebra-20261025T1910/replay.py').read_text(encoding='utf-8')
i=oldrunner.index('heads=');j=oldrunner.index('commands=',i)
oldrunner=oldrunner[:i]+"heads=['all_widths','paired_F2','Word.image_eq_four','Corner.conserved_rectangle','Descent.shorter_conserved']\n"+oldrunner[j:]
(root/'replay.py').write_text(oldrunner,encoding='utf-8')
out={'source_of_adaptation':str(source),'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'proof_sha256':hashlib.sha256(text.encode('utf-8')).hexdigest(),'lines':len(text.splitlines()),
 'new_claim':'Arbitrary coordinate sets and abelian coefficient groups, four-step local-current form.',
 'verified':False,'full_problem_solved':False}
(root/'product-proof-preparation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
