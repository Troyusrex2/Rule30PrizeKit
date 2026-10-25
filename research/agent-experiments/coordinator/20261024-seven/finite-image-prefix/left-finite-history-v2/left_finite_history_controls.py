"""Independent physical language and exact energy controls for deeper past."""
import itertools,json,random,os
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from left_finite_past_controls import physical,pair,energy
from left_lookahead_graph import allowed_word
from left_finite_history_graph import graph,outputs,prefixes
from left_finite_history_exact_rank import synth

def trajectory(word,depth):
 rows=[word];past=[]
 for i in range(depth+1):
  one=physical(rows[-1]);past.append(one[0]);rows.append(physical(one))
 return rows,past

def accepts(word,r,b,H,depth):
 rows,free=trajectory(word,depth)
 if not all(w[0] for w in rows):return False
 contexts=set(range(5))
 for bit in free[:depth]:
  contexts={q+1 if bit else 0 for q in contexts if (bit and q<4) or (not bit and q>0)}
 return r in contexts and free[depth]==b and allowed_word(rows[depth],r,H)

def instrument(T,r,b,H,depth):
 states,edges,terminals,live=graph(T,r,b,H,depth);lookup={}
 for u,v,cur,aft in edges:
  x=states[v][0][0][1][-1];assert (u,x) not in lookup;lookup[u,x]=(v,cur,aft)
 return states,lookup,terminals

def path(word,lookup):
 u=0;edges=[]
 for x in word:
  if (u,x) not in lookup:return -1,edges
  e=lookup[u,x];edges.append(e);u=e[0]
 return u,edges

def controls():
 words=[]
 for n in range(1,12):
  words += [[1]] if n==1 else [[1]+list(w)+[1] for w in itertools.product(range(2),repeat=n-2)]
 physical_checks=language=generated=0
 for depth in [1,2,3]:
  for word in words:
   rows,_=trajectory(word,depth);got=outputs(word,depth)
   if all(w[0] for w in rows):assert got==(rows[-2],rows[-1])
   else:assert got is None
   physical_checks+=1
  for H in [1,2]:
   for r in range(5):
    for b in range(2):
     if b==0 and r==0 or b==1 and r==4:continue
     _,lookup,terminals=instrument(np.zeros((1,2),dtype=np.int16),r,b,H,depth)
     for word in words:
      u,_=path(word,lookup);assert (u in terminals)==accepts(word,r,b,H,depth),(depth,H,r,b,word)
      language+=1
 # Larger horizons are checked with actual reconstructed and mutated words.
 for depth in [1,2,3]:
  for r in range(5):
   for b in range(2):
    if b==0 and r==0 or b==1 and r==4:continue
    _,lookup,terminals=instrument(np.zeros((1,2),dtype=np.int16),r,b,13,depth)
    for prefix in sorted(prefixes(r,b,13,depth)[0]):
     for flip in [-1,1,len(prefix)-1]:
      word=list(prefix)
      if flip>=0:word[flip]^=1
      while word and not word[-1]:word.pop()
      u,_=path(word,lookup);assert (u in terminals)==accepts(word,r,b,13,depth)
      generated+=1
 T=np.array([[((p<<1)|x)&7 for x in range(2)] for p in range(8)],dtype=np.int16);rng=random.Random(3052);C={(r,p,x):Q(rng.randrange(-6,7)) for r in range(5) for p in range(8) for x in range(2)};offset=[Q(rng.randrange(-6,7)) for _ in range(5)];identities=endpoints=0
 for depth in [1,2,3]:
  for r in range(5):
   for b in range(2):
    if b==0 and r==0 or b==1 and r==4:continue
    _,lookup,terminals=instrument(T,r,b,2,depth);future=r+1 if b else 0;reward=0 if b else 4-r
    for word in words:
     u,edges=path(word,lookup)
     if u not in terminals:continue
     cur,aft=outputs(word,depth);p,q,ct,at=terminals[u]
     for lam in [Q(1),Q(3,2),Q(2)]:
      ec,pc=energy(T,C,offset,r,cur,lam);ea,qa=energy(T,C,offset,future,aft,lam)
      assert (p,q)==(pc,qa);endpoints+=1
      z=Q(reward)+offset[future]-offset[r];lower=Q(0)
      for v,cc,aa in edges:
       z=z/lam-sum((C[r,pp,x]/lam**(2*depth+1) for pp,x in cc),Q(0))+sum((C[future,qq,y]/lam**(2*depth+3) for qq,y in aa),Q(0))
       lower=lower/lam+sum((C[r,pp,x]/lam**(2*depth+1) for pp,x in cc),Q(0))
      z-=sum((lam**(2*depth-len(ct)+k)*C[r,pp,x] for k,(pp,x) in enumerate(ct)),Q(0))
      z+=sum((lam**(2*depth+2-len(at)+k)*C[future,qq,y] for k,(qq,y) in enumerate(at)),Q(0))
      lower+=sum((lam**(2*depth-len(ct)+k)*C[r,pp,x] for k,(pp,x) in enumerate(ct)),Q(0))
      assert z==(reward+ea-ec)/lam**len(word)
      assert lower==(ec-offset[r])/lam**len(word)
      identities+=2
 graph_result={'finite_history_depths':[1,2,3],'literal_rule_full_front_checks':physical_checks,'exhaustive_finite_history_language_checks':language,'large_horizon_reconstructed_mutated_paths':generated,'reader_endpoints':endpoints,'exact_geometric_path_identities':identities,'graph_controls_passed':True,'Lean_verified':False}
 (Path(__file__).resolve().parent/'finite-history-graph-controls.json').write_text(json.dumps(graph_result,indent=2)+'\n',encoding='utf-8')
 print('Independent graph controls complete: '+json.dumps(graph_result),flush=True)
 if os.environ.get('RULE30_GRAPH_CONTROLS_ONLY')=='1':return graph_result
 calibrations=[]
 for lam in [Q(1),Q(2)]:
  for direction,zero in [(-1,False),(1,True)]:
   r=synth(np.zeros((1,2),dtype=np.int16),lam,seconds=20,direction=direction,zero=zero,lookahead=2,depth=2)
   assert r['solver_outcome']==('sat' if direction==-1 else 'unsat'),r
   if direction==-1:assert r['exact_rational_graph_certificate']
   calibrations.append({k:v for k,v in r.items() if k not in ['certificate','transition_table']})
 return {**graph_result,'calibrations':calibrations,'all_passed':True}

if __name__=='__main__':
 r=controls();(Path(__file__).resolve().parent/'finite-history-controls.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print(json.dumps(r,indent=2))
