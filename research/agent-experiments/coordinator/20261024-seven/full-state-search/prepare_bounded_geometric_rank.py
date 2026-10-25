"""Version a bounded-below signed rank search and check its geometric gauge.

Allow one fixed additive lower-bound constant, independent of word length.
Set every terminal cost to zero without loss for this family: geometric
gauging replaces E(w) by E(w)-D(start), preserving every rank difference
and existence of a uniform finite lower bound. No CA theorem is claimed.
"""
import hashlib,json,random
from fractions import Fraction as F
from pathlib import Path
from core import save

def main():
 rng=random.Random(302558);checks=0
 for scale in [F(1),F(3,2),F(2),F(3)]:
  T=[[rng.randrange(4) for a in range(4)] for q in range(4)];C=[[rng.randrange(-7,8) for a in range(4)] for q in range(4)];D=[rng.randrange(-7,8) for q in range(4)]
  gauged=[[C[q][a]+scale*D[T[q][a]]-D[q] for a in range(4)] for q in range(4)]
  for _ in range(1000):
   word=[rng.randrange(4) for _ in range(rng.randrange(25))];p=0;v=w=F(0)
   for i,a in enumerate(word):v+=scale**i*C[p][a];w+=scale**i*gauged[p][a];p=T[p][a]
   assert w==v+scale**len(word)*D[p]-D[0];checks+=1
 source=Path('folded_signed_geometric_rank.py').read_text(encoding='utf-8');assert source.count('bounds[lower0]=(0,0)')==1
 source=source.replace('bounds[lower0]=(0,0)','bounds[lower0]=(None,0)\n for l,j in index.items():\n  if l[0]==\'end\':bounds[j]=(0,0)')
 source=source.replace("'global_nonnegativity_on_accepted_language':True","'global_nonnegativity_on_accepted_language':False,'uniform_additive_lower_bound_allowed':True,'terminal_gauge_zero':True")
 source=source.replace('and vals[lower0]==0','and vals[lower0]<=0')
 source=source.replace('folded-signed-geometric-controls.json','folded-bounded-geometric-controls.json').replace('folded-signed-geometric.json','folded-bounded-geometric.json')
 source=source.replace('Signed geometric energy, nonnegative on the whole accepted row language.','Signed geometric energy, uniformly bounded below on the accepted row language.')
 source=source.replace('E(w)>=0','E(w)>=-B').replace('proves E(w)>=-B','proves E(w)>=-B for a fixed finite B').replace('global_nonnegativity_on_accepted_language','global_nonnegativity_on_accepted_language')
 target=Path('folded_bounded_geometric_rank.py');target.write_text(source,encoding='utf-8',newline='\n');compile(source,target.name,'exec')
 save('geometric-gauge-controls.json',{'independent_exact_rational_gauge_identities':checks,'all_passed':True,'Lean_verified':False,'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'original_source_sha256':hashlib.sha256(Path('folded_signed_geometric_rank.py').read_bytes()).hexdigest(),'generated_source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'semantic_changes':['fixed additive lower-bound constant allowed','all terminal values gauged to zero']})
 print({'gauge_controls_passed':checks,'generated':target.name},flush=True)
if __name__=='__main__':main()
