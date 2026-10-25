"""Independently reconstruct the exact three-inequality prefix-rank obstruction."""
import json
from core import HERE,save
from zero_tail_rank import step

def rule(a,b,c):return (30>>((a<<2)|(b<<1)|c))&1

def main():
 cycle=json.loads((HERE/'prefix-monotone-rank-audit.json').read_text())['training']['positive_cycle'];assert len(cycle)==3
 seed=int(cycle[0]['evidence']['right_initial_hex'],16);assert seed==int(cycle[1]['evidence']['right_initial_hex'],16)
 N=10;right={p:seed>>(p-1)&1 for p in range(1,seed.bit_length()+1)};free=[]
 for t in range(2*N):
  old={**right,0:1 if t%2==0 else 0};right={p:rule(old.get(p-1,0),old.get(p,0),old.get(p+1,0)) for p in range(1,max(right)+2)}
  if t%2==0:free.append(1^right[1])
 R=[];Rm=[];spatial=[];verified=[]
 for d,s in enumerate(free):
  before=[a+2*(Rm[j] if j<len(Rm) else 0) for j,a in enumerate(R)]
  r,old=step(R,Rm,1);o=r[-1];R,Rm=step(r,old,s);e=R[-1];spatial +=[o,e]
  after=[a+2*(Rm[j] if j<len(Rm) else 0) for j,a in enumerate(R)]
  if d in [8,9]:
   c=cycle[d-8];assert before==c['before_word'] and after==c['after_word'] and 1-s==c['reward'] and o==e==0
   assert sum(x<<j for j,x in enumerate(free[d-6:d]))==c['before_phase'];assert sum(x<<j for j,x in enumerate(free[d-5:d+1]))==c['after_phase'];verified.append(d)
 short,middle,long=cycle[0]['before_word'],cycle[0]['after_word'],cycle[1]['after_word'];assert long[:len(short)]==short and cycle[0]['after_word']==cycle[1]['before_word']
 left={p:b for p,b in enumerate(spatial,1)}
 for t in range(2*N):
  assert left[1]==(1 if t%2==0 else free[t//2]);old={**left,0:0};left={p:rule(old.get(p+1,0),old.get(p,0),old.get(p-1,0)) for p in range(1,max(left)+2)}
 report={'initial_right_hex':hex(seed),'verified_depths':verified,'short':short,'middle':middle,'long':long,'extension':long[len(short):],
  'phases':[42,21,42],'rewards':[1,0],'right_truth_table_and_scalar_left_reconstruction':True,'full_left_physical_re_evolution':True,
  'scope':'Rules out prefix-monotone phase-conditioned energies with these two descent constraints. A terminal-dependent readout can avoid the prefix-monotonicity premise.',
  'official_evolution_equivalence_formalized':False,'full_problem_solved':False}
 save('prefix-monotone-rank-validation.json',report)
 def literal(w):return '['+','.join(map(str,w))+']'
 source='''import Rule30GoldenCompactBudgetResearch

/-! Algebraic obstruction to prefix-monotone ranks. The two actual examples
are independently physically reconstructed by the companion Python controls.
This module checks the word extension and order contradiction, not the full
Python-to-official-evolution bridge. -/
namespace Rule30PrefixMonotoneRankObstructionResearch
'''
 source+='def shortWord : List Nat := '+literal(short)+'\n\ndef middleWord : List Nat := '+literal(middle)+'\n\ndef longWord : List Nat := '+literal(long)+'\n\ndef extension : List Nat := '+literal(long[len(short):])+'\n\n'
 source+='''theorem long_eq : longWord=shortWord++extension := by rfl

theorem no_prefix_monotone_rank (E : Nat -> List Nat -> Int)
    (hext : forall p xs tail, E p xs <= E p (xs++tail))
    (h0 : E 21 middleWord+1 <= E 42 shortWord)
    (h1 : E 42 longWord <= E 21 middleWord) : False := by
  have hp := hext 42 shortWord extension
  rw [<-long_eq] at hp
  omega

end Rule30PrefixMonotoneRankObstructionResearch
'''
 (HERE/'Rule30PrefixMonotoneRankObstructionResearch.lean').write_text(source,encoding='utf-8',newline='\n')
 print({'exact_physical_cycle_verified':True,'lengths':[len(short),len(middle),len(long)],'extension':report['extension']},flush=True)
if __name__=='__main__':main()
