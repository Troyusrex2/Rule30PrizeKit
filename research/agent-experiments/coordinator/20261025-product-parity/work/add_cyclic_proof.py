from pathlib import Path
import re
root=Path(__file__).resolve().parent
original=Path(r'D:\MWB\Rule30\overnight-20261024\research\agent-experiments\coordinator\20261025-conservation-catalog\Rule30LocalConservation.lean').read_text(encoding='utf-8')
i=original.index('namespace Cycle');j=original.index('end Classification',i)+len('end Classification')
body=original[i:j].replace('List Bool','List (Cell ι)').replace(' : Bool',' : Cell ι')
body=re.sub(r'\bInt\b','G',body);body=re.sub(r'\bfalse\b','zeroCell',body)
body=body.replace('simp only [List.cons_append,weight,run,ih]; omega','simp only [List.cons_append,weight,run,ih]; abel')
body=body.replace('  dsimp only [p]\n  omega',
 '''  dsimp only [p]
  have hh := congrArg₂ (fun x y : G => x-y) h1 h0
  apply sub_eq_zero.mp
  convert hh using 1 <;> abel''')
needle='simpa only [List.drop_one] using (show h (image xs)=h (crop m xs)+p xs.dropLast-p (xs.drop 1) by omega)'
assert needle in body
body=body.replace(needle,'''have result : h (image xs)=h (crop m xs)+p xs.dropLast-p (xs.drop 1) := by
    apply sub_eq_zero.mp
    convert (sub_eq_zero.mpr hh) using 1; abel
  simpa only [List.drop_one] using result''')
needle='      p xs-p (run (shift xs b) bs)\n    omega';assert needle in body
body=body.replace(needle,'      p xs-p (run (shift xs b) bs)\n    abel')
i=body.index('theorem local_conserved_cyclic');j=body.index('theorem trivial_conserved',i)
body=body[:i]+'''theorem local_conserved_cyclic (m : Nat) (h p : List (Cell ι) → G)
    (hc : Conserved m h p) : CyclicConserved m h := by
  have hp : ∀ xs, xs.length=m+7 → ∀ b,
      change m h (xs++[b])=p xs-p (shift xs b) := by
    intro xs hl b
    have hh := conserved_word m h p hc (xs++[b]) (by simp [hl])
    rw [List.dropLast_concat] at hh
    unfold change shift
    rw [List.drop_one]
    apply sub_eq_zero.mp
    convert (sub_eq_zero.mpr hh) using 1; abel
  intro xs hl bs hb
  have hh := gradient_weight (m+7) (change m h) p hp xs bs hl
  rw [hb] at hh
  simpa using hh

'''+body[j:]
needle='  rw [←hc0]\n  omega';assert needle in body
body=body.replace(needle,'  rw [←hc0]\n  abel')
path=root/'Rule30ProductConservationResearch.lean';text=path.read_text(encoding='utf-8')
anchor='/-- All widths, any family';pos=text.index(anchor)
text=text[:pos]+body+'\n\n'+text[pos:]
ending='end Rule30ProductConservationResearch';assert text.endswith(ending+'\n')
aliases='''/-- Exact closed-walk classification, with no assumed local current.
The types are fixed at Type0 here so that the official headline checker can
report the theorem; the library proof above is universe-polymorphic. -/
theorem all_groups (I : Type) (K : Type) [AddCommGroup K]
    (m : Nat) (hm : 0<m) (h : List (Cell I) → K) :
    Cycle.CyclicConserved m h ↔ Triviality.Trivial m h :=
  Classification.cyclic_conserved_iff_trivial m hm h

/-- Every mixed pair parity density, at EVERY width. -/
theorem paired_F2_exact (m : Nat) (hm : 0<m) (h : List (Cell (Fin 2)) → ZMod 2) :
    Cycle.CyclicConserved m h ↔
      ∃ c : ZMod 2, ∃ b : List (Cell (Fin 2)) → ZMod 2, ∀ xs, xs.length=m →
        h xs=c+b xs.tail-b xs.dropLast :=
  Classification.cyclic_conserved_iff_trivial m hm h

/-- The image in the classification is exactly four shrinking Rule30
updates on each coordinate; it is not an independently fitted map. -/
theorem paired_F2_semantics (xs : List (Cell (Fin 2))) :
    Corner.image xs=Corner.four xs := Word.image_eq_four xs

'''
text=text[:-len(ending+'\n')]+aliases+ending+'\n'
path.write_text(text,encoding='utf-8',newline='\n')
runner=root/'replay.py';r=runner.read_text(encoding='utf-8');i=r.index('heads=');j=r.index('commands=',i)
r=r[:i]+"heads=['all_groups','paired_F2_exact','paired_F2','paired_F2_semantics']\n"+r[j:]
runner.write_text(r,encoding='utf-8')
print('Added exact cyclic classification and concrete official headlines; no checker changes.')
