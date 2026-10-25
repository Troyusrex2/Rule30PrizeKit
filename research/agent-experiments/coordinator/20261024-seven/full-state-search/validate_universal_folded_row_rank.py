"""Independent full physical updates for center-out folded spatial words."""
import itertools,random
from core import save
from universal_folded_row_rank import advance,updated

def physical(word):
 N=len(word)-1;row={0:1}
 for d,x in enumerate(word[1:],1):row[-d]=x&1;row[d]=x>>1
 center=[]
 for t in range(2):
  row={p:(30>>((row.get(p-1,0)<<2)|(row.get(p,0)<<1)|row.get(p+1,0)))&1 for p in range(-N-t-1,N+t+2)};center.append(row[0])
 return [row[-d]+2*row[d] for d in range(N+3)],center

def main():
 rng=random.Random(302549);T=[[rng.randrange(5) for x in range(4)] for p in range(5)];C=[[rng.randrange(-5,6) for x in range(4)] for p in range(5)];D=[rng.randrange(-5,6) for p in range(5)];checked=accepted=0
 def E(w):
  p=0;v=0
  for x in w:v+=C[p][x];p=T[p][x]
  return v+D[p]
 for N in range(7):
  for tail in itertools.product(range(4),repeat=N):
   if N and not tail[-1]:continue
   word=[3]+list(tail);actual,center=physical(word);computed=updated(word);good=center==[0,1]
   assert (computed is not None)==good;checked+=1
   if not good:continue
   assert computed==actual and len(computed)==len(word)+2 and computed[0]==3 and computed[-1]!=0;accepted+=1
   stage=0;buf=();p=q=0;v=0
   for x in word:
    stage,buf,y=advance(stage,buf,x);v-=C[p][x];p=T[p][x]
    if y is not None:v+=C[q][y];q=T[q][y]
   for _ in range(4):
    stage,buf,y=advance(stage,buf,0)
    if y is not None:v+=C[q][y];q=T[q][y]
   assert v+D[q]-D[p]==E(computed)-E(word)
 report={'canonical_folded_words':checked,'accepted_1_to_0_to_1_words':accepted,'physical_two_step_updates_and_signed_path_identities_passed':True,'all_passed':True,'Lean_verified':False,'full_problem_solved':False};save('universal-folded-row-physical-controls.json',report);print(report,flush=True)
if __name__=='__main__':main()
