"""Every policy's chosen earlier score is an actual before-word prefix."""
import itertools,random
from pathlib import Path
import json
import numpy as np
from universal_folded_row_rank import advance,updated
from universal_folded_prefix_peak_lagged import suffix_paths,post_states
from folded_peak_policy import synth

def main():
 rng=random.Random(302554);T=np.ones((3,4),dtype=np.int16);T[1:]=1+np.array([[rng.randrange(2) for x in range(4)] for p in range(2)]);C=[[rng.randrange(-5,6) for x in range(4)] for p in range(3)];post=post_states(T);postindex={p:i for i,p in enumerate(sorted(post))};count=0
 def scores(w):
  p=0;s=0;ss=[0];pp=[0]
  for x in w:s+=C[p][x];p=int(T[p,x]);ss.append(s);pp.append(p)
  return ss,pp
 for N in range(5):
  for tail in itertools.product(range(4),repeat=N):
   if N and not tail[-1]:continue
   word=[3]+list(tail);after=updated(word)
   if after is None:continue
   S,P=scores(word);A,Q=scores(after);stage=0;buf=();j=0
   for i,x in enumerate(word,1):
    stage,buf,y=advance(stage,buf,x)
    if y is None:continue
    j+=1;actual=(P[i-1],word[i-1]);assert [actual] in suffix_paths(T,P[i],buf,1,post)
    for policy in range(1<<(4*len(post))):
     previous=(policy>>(4*postindex[actual[0]]+actual[1]))&1;matched=i-previous
     assert A[j]-S[i]+(C[actual[0]][actual[1]] if previous else 0)==A[j]-S[matched];count+=1
   oldbuf=buf
   for _ in range(4):
    stage,buf,y=advance(stage,buf,0)
    if y is None:continue
    j+=1;actual=(P[-2],word[-1]);assert [actual] in suffix_paths(T,P[-1],oldbuf,1,post)
    for policy in range(1<<(4*len(post))):
     previous=(policy>>(4*postindex[actual[0]]+actual[1]))&1;matched=len(word)-previous
     assert A[j]-S[-1]+(C[actual[0]][actual[1]] if previous else 0)==A[j]-S[matched];count+=1
 pos=synth(np.zeros((1,4),dtype=np.int16),0,toy=True);neg=synth(np.ones((2,4),dtype=np.int16),0,fixed_zero=True)
 assert pos.get('exact_rational_graph_certificate') and pos['reward_rate']>.999999
 assert neg['solver_status']==0 and abs(neg['reward_rate'])<1e-8
 report={'matched_prefix_identities_all_policies':count,'toy_deletion_positive':pos,'actual_zero_energy_negative':neg,'all_passed':True,'Lean_verified':False,'full_problem_solved':False}
 (Path(__file__).resolve().parent/'folded-peak-policy-controls.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print({'matched_prefix_identities':count,'positive_and_negative_controls':'pass'},flush=True)
if __name__=='__main__':main()
