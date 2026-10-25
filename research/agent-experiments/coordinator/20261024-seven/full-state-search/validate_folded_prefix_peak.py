"""Check every matched prefix score against independent direct prefix sums."""
import itertools,random
from core import save
from universal_folded_row_rank import advance,updated

def main():
 rng=random.Random(302552);T=[[rng.randrange(4) for x in range(4)] for p in range(4)];C=[[rng.randrange(-5,6) for x in range(4)] for p in range(4)];count=words=0
 def scores(w):
  p=0;s=0;out=[0]
  for x in w:s+=C[p][x];p=T[p][x];out.append(s)
  return out
 for N in range(6):
  for tail in itertools.product(range(4),repeat=N):
   if N and not tail[-1]:continue
   before=[3]+list(tail);after=updated(before)
   if after is None:continue
   S=scores(before);A=scores(after);stage=0;buf=();p=q=0;delta=0;j=0
   for i,x in enumerate(before,1):
    stage,buf,y=advance(stage,buf,x);delta-=C[p][x];p=T[p][x]
    if y is not None:delta+=C[q][y];q=T[q][y];j+=1;assert delta==A[j]-S[i];count+=1
   for _ in range(4):
    stage,buf,y=advance(stage,buf,0)
    if y is not None:delta+=C[q][y];q=T[q][y];j+=1;assert delta==A[j]-S[-1];count+=1
   assert j==len(after);words+=1
 report={'actual_good_folded_words':words,'independent_matched_prefix_identities':count,'all_passed':True,'Lean_verified':False,'full_problem_solved':False};save('folded-prefix-peak-physical-controls.json',report);print(report,flush=True)
if __name__=='__main__':main()
