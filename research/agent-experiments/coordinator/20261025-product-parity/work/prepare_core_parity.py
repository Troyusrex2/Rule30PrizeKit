"""Port the verified F2 specialization to the catalog's core-only arithmetic."""
from pathlib import Path
import re
root=Path(__file__).resolve().parent
source=root/'Rule30ProductConservationResearch.lean'
text=source.read_text(encoding='utf-8').replace('Rule30ProductConservationResearch','Rule30ProductParityResearch')
for line in ['public import Mathlib.Data.ZMod.Basic\n','public import Mathlib.Tactic.Abel\n','public import Mathlib.Tactic.Convert\n']:
    assert line in text;text=text.replace(line,'')
text=text.replace('public import Ruliology.CellularAutomata.Rule30Prize','public import Init.Data.Fin.Lemmas\npublic import Ruliology.CellularAutomata.Rule30Prize')
text=text.replace('universe u v','universe u').replace('variable {ι : Type u} {G : Type v} [AddCommGroup G]','variable {ι : Type u}')
text=re.sub(r'\bG\b','(Fin 2)',text).replace('ZMod 2','Fin 2')
# Fin2 identities are discharged by the core Presburger tactic after exposing
# values. The final proof is checked by the same kernel as the general proof.
text=re.sub(r'^\s*have hh := congrArg₂ .*\n','\n',text,flags=re.M)
text=re.sub(r'^([ ]*)apply sub_eq_zero\.mp\n','',text,flags=re.M)
text=re.sub(r'^([ ]*)convert .* using 1(?: <;>|;) abel\n',r'\1parity\n',text,flags=re.M)
text=text.replace('  exact sub_right_inj.mp (h0.symm.trans h1)','  parity')
text=re.sub(r'\babel\b','parity',text)
i=text.index('/-- Exact closed-walk classification');j=text.index('/-- Every mixed pair parity density',i)
text=text[:i]+'''/-- Arbitrarily many Boolean coordinates and every positive window width.
The concrete headline is monomorphic; the library above permits any universe. -/
theorem all_ensembles (I : Type) (m : Nat) (hm : 0<m)
    (h : List (Cell I) → Fin 2) :
    Cycle.CyclicConserved m h ↔ Triviality.Trivial m h :=
  Classification.cyclic_conserved_iff_trivial m hm h

'''+text[j:]
i=text.index('/-!');j=text.index('-/',i)+2
text=text[:i]+'''/-!
All-width mod-two local conservation classification for any coordinatewise
product of Rule30. Every cyclically conserved finite-window parity score is
constant plus a spatial coboundary. The converse is included. No fixed window
cutoff, local-current hypothesis, or finite-ring census is a premise.

The conserved change is for FOUR shrinking Rule30 steps, as the semantics
theorem verifies. This rules out a class of parity-charge strategies; it does
not solve a Rule30 prize problem or rule out every possible invariant.

This core-only specialization follows the accompanying verified arbitrary-
abelian-group proof. Both extend the earlier integer scalar range-reduction
argument. Proof and formalization: Troy Lowry with OpenAI Codex. No claim of
literature novelty is made.
-/'''+text[j:]
anchor='variable {ι : Type u}\n';assert text.count(anchor)==1
arithmetic='''
@[simp] theorem p_add_sub_cancel : ∀ a b : Fin 2, a+b-b=a := by decide +kernel
@[simp] theorem p_zero_add : ∀ a : Fin 2, 0+a=a := by decide +kernel
@[simp] theorem p_add_zero : ∀ a : Fin 2, a+0=a := by decide +kernel
@[simp] theorem p_sub_zero : ∀ a : Fin 2, a-0=a := by decide +kernel
@[simp] theorem p_sub_self : ∀ a : Fin 2, a-a=0 := by decide +kernel

macro "parity" : tactic => `(tactic|
  (simp only [Fin.ext_iff,Fin.val_add,Fin.val_sub,Fin.val_zero] at *; omega))

'''
text=text.replace(anchor,anchor+arithmetic)
assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide|Mathlib|AddCommGroup|ZMod)\b|skipKernel|decide\s*\+native',text)
(root/'Rule30ProductParityResearch.lean').write_text(text,encoding='utf-8',newline='\n')
runner=(root/'replay.py').read_text(encoding='utf-8')
i=runner.index('heads=');j=runner.index('commands=',i)
runner=runner[:i]+"heads=['all_ensembles','paired_F2_exact','paired_F2','paired_F2_semantics']\n"+runner[j:]
(root/'replay_parity.py').write_text(runner,encoding='utf-8')
print('Prepared core-only parity specialization; it has not yet been accepted.')
