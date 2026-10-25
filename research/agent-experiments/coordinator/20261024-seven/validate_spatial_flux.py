"""Independent small truth-table and column-invariant controls for flux searches."""
import itertools
from core import save
from spatial_flux_rank_valid import valid,after
from spatial_flux_rank_three_columns import words,after as after3,boundary

def main():
 gates=0
 for a,b,c in itertools.product(range(2),repeat=3):
  y=(30>>((a<<2)|(b<<1)|c))&1;assert y^(b|c)==a;gates+=1
 pairs=0
 for L in range(1,6):
  for w in itertools.product(range(4),repeat=L):
   if valid(w):assert valid(after(w));pairs+=1
 triples=0
 def good(w):return all((w[j]&1)==(((w[j+1]>>1)&1)^(((w[j]>>1)&1)|(w[j]>>2))) for j in range(len(w)-1))
 for L in range(1,6):
  for w in words(L):
   assert good(w) and good(after3(w));triples+=1
 boundaries=0
 for n in range(1,7):
  for f in itertools.product(range(2),repeat=n):assert good(boundary(f));boundaries+=1
 save('spatial-flux-controls.json',{'inverse_truth_table_cases':gates,'pair_invariant_cases':pairs,'triple_invariant_cases':triples,'boundary_cases':boundaries,'all_passed':True,'Lean_verified':False,'full_problem_solved':False})
 print({'gates':gates,'pairs':pairs,'triples':triples,'boundaries':boundaries,'all_passed':True},flush=True)
if __name__=='__main__':main()
