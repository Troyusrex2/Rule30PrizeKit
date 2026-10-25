"""Use core finite-field identities and AC simplification, never native proofs."""
from pathlib import Path
import re,shutil
root=Path(__file__).resolve().parent
old=root/'Rule30ProductParityResearch.lean';failed=root/'evidence/attempt04-core-omega'
failed.mkdir(exist_ok=True);shutil.copyfile(old,failed/'source.lean')
for name,dest in [('evidence/replay_parity.guard.json','guard.json'),
                  ('evidence/Rule30ProductParityResearch/build.log','build.log'),
                  ('core-omega-stop.json','manual-stop.json')]:
    if (root/name).exists():shutil.copyfile(root/name,failed/dest)
text=(root/'Rule30ProductConservationResearch.lean').read_text(encoding='utf-8')
text=text.replace('Rule30ProductConservationResearch','Rule30ProductParityResearch')
for line in ['public import Mathlib.Data.ZMod.Basic\n','public import Mathlib.Tactic.Abel\n','public import Mathlib.Tactic.Convert\n']:
    assert line in text;text=text.replace(line,'')
text=text.replace('public import Ruliology.CellularAutomata.Rule30Prize','public import Init.Data.Fin.Lemmas\npublic import Ruliology.CellularAutomata.Rule30Prize')
text=text.replace('universe u v','universe u').replace('variable {ι : Type u} {G : Type v} [AddCommGroup G]','variable {ι : Type u}')
text=re.sub(r'\bG\b','(Fin 2)',text).replace('ZMod 2','Fin 2')
rules='p_sub_as_add,p_add_assoc,p_add_comm,p_add_left_comm,p_cancel_pair,p_add_self,p_add_zero,p_zero_add'
text=re.sub(r'^([ ]*)convert (.+) using 1(?: <;>|;) abel$',
            lambda m:m[1]+'simpa only ['+rules+'] using '+m[2],text,flags=re.M)
text=re.sub(r'\babel\b','rule30_parity_nf',text)
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
constant plus a spatial coboundary, and conversely. The conserved change is
for FOUR shrinking Rule30 steps, as the semantics theorem verifies.

No fixed window cutoff, local-current hypothesis, or finite-ring census is
a premise. This rules out a parity-charge strategy; it does not solve a prize
problem or rule out every kind of invariant. This core-only specialization
follows the accompanying arbitrary-abelian-group proof; both extend the
earlier integer scalar range-reduction argument.

Proof and formalization: Troy Lowry with OpenAI Codex. No literature novelty
is claimed. Coefficients are Fin2 with their core modular addition/subtraction.
-/'''+text[j:]
arithmetic='''
theorem sub_eq_zero : ∀ {a b : Fin 2}, a-b=0 ↔ a=b := by decide +kernel
theorem sub_right_inj : ∀ {a b c : Fin 2}, a-b=a-c ↔ b=c := by decide +kernel
@[simp] theorem p_add_sub_cancel : ∀ a b : Fin 2, a+b-b=a := by decide +kernel
@[simp] theorem p_zero_add : ∀ a : Fin 2, 0+a=a := by decide +kernel
@[simp] theorem p_add_zero : ∀ a : Fin 2, a+0=a := by decide +kernel
@[simp] theorem p_sub_zero : ∀ a : Fin 2, a-0=a := by decide +kernel
@[simp] theorem p_sub_self : ∀ a : Fin 2, a-a=0 := by decide +kernel
theorem p_sub_as_add : ∀ a b : Fin 2, a-b=a+b := by decide +kernel
theorem p_add_assoc : ∀ a b c : Fin 2, (a+b)+c=a+(b+c) := by decide +kernel
theorem p_add_comm : ∀ a b : Fin 2, a+b=b+a := by decide +kernel
theorem p_add_left_comm : ∀ a b c : Fin 2, a+(b+c)=b+(a+c) := by decide +kernel
theorem p_cancel_pair : ∀ a b : Fin 2, a+(a+b)=b := by decide +kernel
theorem p_add_self : ∀ a : Fin 2, a+a=0 := by decide +kernel

macro "rule30_parity_nf" : tactic => `(tactic|
  simp only [p_sub_as_add,p_add_assoc,p_add_comm,p_add_left_comm,p_cancel_pair,
    p_add_self,p_add_zero,p_zero_add])

'''
anchor='variable {ι : Type u}\n';assert text.count(anchor)==1;text=text.replace(anchor,anchor+arithmetic)
assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide|Mathlib|AddCommGroup|ZMod|convert|abel)\b|skipKernel|decide\s*\+native',text)
old.write_text(text,encoding='utf-8',newline='\n')
print('Prepared core-only parity AC proof; not yet verified.')
