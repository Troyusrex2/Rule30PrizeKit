"""Independently validate the reader-product graph identities on concrete words."""
import itertools,random
import numpy as np
from core import save
from spatial_flux_rank_three_columns import words,after,boundary,zero_runs

def main():
 rng=random.Random(302532);spatial=boundary_count=0
 for K in [1,2,4,7]:
  T=[[rng.randrange(K) for a in range(8)] for p in range(K)];C=[[rng.randrange(-9,10) for a in range(8)] for p in range(K)];D=[rng.randrange(-9,10) for p in range(K)];D[0]=0
  def energy(w):
   state=0;v=0
   for a in w:v+=C[state][a];state=T[state][a]
   return v+D[state]
  for L in range(1,6):
   for w in words(L):
    p=T[0][w[0]];q=0;score=C[0][w[0]]
    for last,token in zip(w,w[1:]):
     # Compute inverse Rule 30 with four scalar cells, independently of BFS.
     a=last%2;b=(last//2)%2;future=token%2
     left=future^(a|b);o=left+2*a+4*b
     assert o==after((last,token))[0]
     score+=C[p][token]-C[q][o];p=T[p][token];q=T[q][o]
    score+=D[p]-D[q]
    assert score==energy(w)-energy(after(w));spatial+=1
  for n in range(1,8):
   for f in itertools.product(range(2),repeat=n):
    p=0;prev=1;score=0
    for s in f:
     mid=T[p][5];score+=C[p][5]+C[mid][5*s]-int(prev==1 and s==0);p=T[mid][5*s];prev=s
    assert score+D[p]==energy(boundary(f))-zero_runs(f);boundary_count+=1
 save('universal-spatial-reader-controls.json',{'random_signed_reader_tables':4,'spatial_path_identity_cases':spatial,'boundary_path_identity_cases':boundary_count,'all_passed':True,'Lean_verified':False,'full_problem_solved':False})
 print({'spatial_identities':spatial,'boundary_identities':boundary_count,'all_passed':True},flush=True)
if __name__=='__main__':main()
