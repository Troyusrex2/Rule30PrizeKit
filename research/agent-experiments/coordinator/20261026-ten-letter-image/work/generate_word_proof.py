from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
data=json.loads((ROOT/'word-tree-odd.json').read_bytes());assert data['unsat']
out=['''module
public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

/-! A ten-letter actual-image obstruction found while testing the delayed
defect family against the round-three realizability question. The finite
case proof checks every local relation in Lean; no solver result is trusted.
The uniform corollary applies to infinite as well as finite right halves.
This does not settle P1, CQ01 or the canonical center observer. -/
@[expose] public section
namespace Rule30IsolatedDefectResearch
open Ruliology.CellularAutomata
open Rule30Jen Rule30PeriodTwoSideways Rule30PeriodTwoCoupled
open Rule30Ether (drv drv_col0)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def word : List Bool := [true,false,true,false,true,true,true,false,true,false]

theorem no_profile (c : Nat → Nat → Bool)
    (hs : ∀ t p, c (t+1) (p+1)=rule (c t p) (c t (p+1)) (c t (p+2)))
    (hb : ∀ t, c t 0=decide (t%2=1))
    (hw : ∀ i, i<10 → c (2*i) 1= !(word.getD i false)) : False := by''']
count=0
def cell(k):return f'c {k[0]} {k[1]}'
def new():
    global count
    count+=1;return 'v'+str(count)
known={}
for r in data['initial']:
    k=tuple(r['cell']);name=new();known[k]=name;b=str(bool(r['value'])).lower()
    proof=f'by simpa using hb {k[0]}' if k[1]==0 else f'by simpa [word] using hw {k[0]//2} (by decide)'
    out.append(f'  have {name} : {cell(k)}={b} := {proof}')

def emit(tree,known,indent):
    known=dict(known);pad=' '*indent
    for step in tree['steps']:
        k=tuple(step['cell']);name=new();rel=[tuple(q) for q in step['relation']]
        prem={tuple(p['cell']):p['value'] for p in step['premises']}
        assert k not in prem and all(q in known for q in prem)
        unknown=[q for q in rel if q not in prem]
        out.append(f'{pad}have {name} : {cell(k)}={str(bool(step["value"])).lower()} := by')
        out.append(f'{pad}  have he := hs {rel[1][0]} {rel[1][1]}')
        if prem:out.append(f'{pad}  rw [{", ".join(known[q] for q in prem)}] at he')
        out.append(f'{pad}  revert he')
        out.append(pad+'  '+' <;> '.join([f'cases {cell(q)}' for q in unknown]+['decide +kernel']))
        known[k]=name
    if 'conflict' in tree:
        rel=[tuple(q) for q in tree['conflict']]
        out.append(f'{pad}have he := hs {rel[1][0]} {rel[1][1]}')
        out.append(f'{pad}rw [{", ".join(known[q] for q in rel if q in known)}] at he')
        out.append(f'{pad}revert he')
        out.append(pad+' <;> '.join([f'cases {cell(q)}' for q in rel if q not in known]+['decide +kernel']))
    else:
        k=tuple(tree['split']);name=new()
        out.append(f'{pad}cases {name} : {cell(k)} with')
        for tag,branch in zip(['false','true'],tree['branches']):
            out.append(f'{pad}| {tag} =>')
            emit(branch,{**known,k:name},indent+2)
emit(data['tree'],known,2)
out.append('''
theorem no_free_1010111010 (R : Nat → Bool) (s : Nat) :
    (List.range 10).map (fun i => !u R (s+i)) ≠ word := by
  intro h
  let c : Nat → Nat → Bool := fun t p => drv altCol R (2*s+1+t) p
  apply no_profile c
  · intro t p
    dsimp [c]
    rw [show 2*s+1+(t+1)=2*s+1+t+1 by omega]
    rfl
  · intro t
    dsimp [c]
    rw [drv_col0]
    unfold altCol
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq]
    omega
  · intro i hi
    have hh := congrArg (fun l : List Bool => l.getD i false) h
    have hv : (!u R (s+i))=word.getD i false := by
      simpa [List.getD_eq_getElem?_getD,hi] using hh
    have hv' : u R (s+i)= !(word.getD i false) := by
      cases hu : u R (s+i) <;> cases hw : word.getD i false <;> simp_all
    dsimp [c]
    unfold u at hv'
    rw [show 2*(s+i)+1=2*s+1+2*i by omega] at hv'
    exact hv'

def singleFlip (L s : Nat) : Bool := if s=L then true else decide (s%2=1)

theorem isolated_word (L : Nat) (hL : 6≤L) (he : L%2=0) :
    (List.range 10).map (fun i => singleFlip L (L-5+i))=word := by
  have hv (i : Nat) (hi : i<10) :
      singleFlip L (L-5+i)=decide (i=0 ∨ i=2 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=8) := by
    unfold singleFlip
    by_cases h : L-5+i=L
    · rw [if_pos h]
      have : i=5 := by omega
      simp [this]
    · rw [if_neg h]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
  have hr : List.range 10=[0,1,2,3,4,5,6,7,8,9] := by decide +kernel
  have h0 : singleFlip L (L-5)=true := by simpa using hv 0 (by omega)
  rw [hr]
  simp only [List.map_cons,List.map_nil]
  simp [word,h0,hv 1 (by omega),hv 2 (by omega),hv 3 (by omega),
    hv 4 (by omega),hv 5 (by omega),hv 6 (by omega),hv 7 (by omega),hv 8 (by omega),hv 9 (by omega)]

theorem no_actual_isolated_flip (L : Nat) (hL : 6≤L) (he : L%2=0)
    (R : Nat → Bool) : ¬ (∀ s, (!u R s)=singleFlip L s) := by
  intro h
  apply no_free_1010111010 R (L-5)
  simpa only [h] using isolated_word L hL he

theorem delayed_family_not_actual (j : Nat) (hj : 0<j) (R : Nat → Bool) :
    ¬ (∀ s, (!u R s)=singleFlip (4*j+2) s) :=
  no_actual_isolated_flip (4*j+2) (by omega) (by omega) R

end Rule30IsolatedDefectResearch
''')
source='\n'.join(out)+'\n'
(ROOT/'Rule30IsolatedDefectResearch.lean').write_text(source,encoding='utf-8')
print(json.dumps({'case_tree_nodes':data['nodes'],'local_facts_and_split_names':count,'lines':len(source.splitlines())}))
