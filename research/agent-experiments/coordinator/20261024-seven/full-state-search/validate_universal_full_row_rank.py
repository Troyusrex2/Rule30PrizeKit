"""Exhaustive small physical updates and weighted path identities for row ranks."""
import itertools,random
from core import save
from universal_full_row_rank import emit,updated,rule

def physical(word):
 mark=word.index(3);row={j:x&1 for j,x in enumerate(word)};middle=[]
 for t in range(2):
  row={j:(30>>((row.get(j-1,0)<<2)|(row.get(j,0)<<1)|row.get(j+1,0)))&1 for j in range(-t-1,len(word)+t+1)};middle.append(row[mark])
 return [row[j]+(2 if j==mark else 0) for j in range(-2,len(word)+2)],middle

def main():
 rng=random.Random(302548);T=[[rng.randrange(5) for _ in range(4)] for p in range(5)];C=[[rng.randrange(-6,7) for _ in range(4)] for p in range(5)];D=[rng.randrange(-6,7) for _ in range(5)];checked=accepted=identities=0
 def E(w):
  p=0;v=0
  for x in w:v+=C[p][x];p=T[p][x]
  return v+D[p]
 for n in range(1,10):
  for bits in itertools.product((0,1),repeat=max(0,n-2)):
   raw=[1] if n==1 else [1]+list(bits)+[1]
   for mark in range(n):
    if not raw[mark]:continue
    word=raw[:];word[mark]=3;actual,center=physical(word);computed=updated(word);good=center==[0,1]
    assert (computed is not None)==good;checked+=1
    if not good:continue
    assert computed==actual and len(computed)==len(word)+4 and computed[0]&1 and computed[-1]&1;accepted+=1
    buf=(0,0,0,0);p=q=0;value=0
    for x in word:
     buf,y=emit(buf,x);value+=C[q][y]-C[p][x];p=T[p][x];q=T[q][y]
    for _ in range(4):buf,y=emit(buf,0);value+=C[q][y];q=T[q][y]
    value+=D[q]-D[p];assert value==E(computed)-E(word);identities+=1
 report={'canonical_marked_words':checked,'accepted_1_to_0_to_1_words':accepted,'independent_physical_updates_passed':True,'signed_path_identities':identities,'all_passed':True,'Lean_verified':False,'full_problem_solved':False};save('universal-full-row-physical-controls.json',report);print(report,flush=True)
if __name__=='__main__':main()
