"""Compare every simulated match to direct prefix sums and actual DFA states."""
import itertools,random
import numpy as np
from core import save
from universal_folded_row_rank import advance,updated
from universal_folded_prefix_peak_lagged import suffix_paths,post_states,transient

def main():
 rng=random.Random(302553);T=transient(np.array([[rng.randrange(3) for x in range(4)] for p in range(3)],dtype=np.int16));C=[[rng.randrange(-5,6) for x in range(4)] for p in range(len(T))];post=post_states(T);count=words=0
 def scores(w):
  p=0;s=0;ss=[0];pp=[0]
  for x in w:s+=C[p][x];p=int(T[p,x]);ss.append(s);pp.append(p)
  return ss,pp
 for N in range(6):
  for tail in itertools.product(range(4),repeat=N):
   if N and not tail[-1]:continue
   word=[3]+list(tail);after=updated(word)
   if after is None:continue
   S,P=scores(word);A,Q=scores(after);stage=0;buf=();j=0
   for i,x in enumerate(word,1):
    stage,buf,y=advance(stage,buf,x)
    if y is None:continue
    j+=1
    for h in [0,1,2]:
     matched=j+h;paths=suffix_paths(T,P[i],buf,i-matched,post);actual=[(P[k],word[k]) for k in range(matched,i)];assert actual in paths
     assert A[j]-S[i]+sum(C[p][z] for p,z in actual)==A[j]-S[matched];count+=1
   endbuf=buf
   for _ in range(4):
    stage,buf,y=advance(stage,buf,0)
    if y is None:continue
    j+=1
    for h in [0,1,2]:
     matched=min(j+h,len(word));paths=suffix_paths(T,P[-1],endbuf,len(word)-matched,post);actual=[(P[k],word[k]) for k in range(matched,len(word))];assert actual in paths
     assert A[j]-S[-1]+sum(C[p][z] for p,z in actual)==A[j]-S[matched];count+=1
   words+=1
 report={'actual_good_words':words,'all_offsets_prefix_matches_checked':count,'reader_preimages_include_actual_history':True,'all_passed':True,'Lean_verified':False,'full_problem_solved':False};save('folded-prefix-peak-lagged-physical-controls.json',report);print(report,flush=True)
if __name__=='__main__':main()
