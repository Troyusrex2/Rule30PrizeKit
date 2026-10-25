"""Exact physical phase assignment and rational phase-energy controls."""
import itertools,json,random
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from left_future_history_graph import branches,future_word
from left_finite_past_controls import physical,energy
from left_lookahead_graph import allowed_word
from left_finite_history_graph import outputs
from left_future_history_rank import synth

def accepts(word,r,b,H,depth):
 rows=[word];free=[]
 for _ in range(depth+1):
  one=physical(rows[-1]);free.append(one[0]);rows.append(physical(one))
 if not all(w[0] for w in rows):return False
 contexts=set(range(5))
 for bit in free[:depth]:
  contexts={q+1 if bit else 0 for q in contexts if (bit and q<4) or (not bit and q>0)}
 return r in contexts and free[depth]==b and allowed_word(rows[depth],r,H)

def instrument(T,H,K,depth):
 result=[]
 for before,after,reward,data in branches(T,H,K,depth):
  states,edges,terminals,live=data;lookup={}
  for u,v,cur,aft in edges:
   key=(u,states[v][0][0][1][-1]);assert key not in lookup;lookup[key]=(v,cur,aft)
  result.append((before,after,reward,lookup,terminals))
 return result

def path(word,lookup):
 u=0;edges=[]
 for x in word:
  if (u,x) not in lookup:return -1,edges
  e=lookup[u,x];edges.append(e);u=e[0]
 return u,edges

def controls(depth):
 words=[[1]]
 for n in range(2,12):words.extend([1]+list(w)+[1] for w in itertools.product(range(2),repeat=n-2))
 language=unique=phasechecks=0
 for K in [1,2,3]:
  data=instrument(np.zeros((1,2),dtype=np.int16),4,K,depth)
  for word in words:
   counts={r:0 for r in range(5)}
   for before,after,reward,lookup,terminals in data:
    u,_=path(word,lookup);cur,aft=outputs(word,depth) or (None,None)
    w=None if cur is None else future_word(cur,K+1)
    want=cur is not None and accepts(word,before[0],w[0],4,depth) and before[1]==w[:K] and after==(before[0]+1 if w[0] else 0,w[1:])
    assert (u in terminals)==want,(K,before,after,word)
    if want:
     assert future_word(aft,K)==after[1];phasechecks+=1;counts[before[0]]+=1
    language+=1
   for r,count in counts.items():
    cur,aft=outputs(word,depth) or (None,None);b=None if cur is None else physical(cur)[0]
    assert count==int(b is not None and accepts(word,r,b,4,depth))
    unique+=1
 T=np.array([[((p<<1)|x)&7 for x in range(2)] for p in range(8)],dtype=np.int16);data=instrument(T,4,2,depth);phases=sorted({p for a,b,_,_,_ in data for p in [a,b]});rng=random.Random(302055)
 C={(r,p,x):Q(rng.randrange(-9,10)) for r in phases for p in range(8) for x in range(2)};offset={r:Q(rng.randrange(-9,10)) for r in phases};identities=endpoints=0
 for before,after,reward,lookup,terminals in data:
  for word in words:
   u,edges=path(word,lookup)
   if u not in terminals:continue
   cur,aft=outputs(word,depth);p,q,ct,at=terminals[u]
   for lam in [Q(1),Q(3,2),Q(2)]:
    ec,pc=energy(T,C,offset,before,cur,lam);ea,qa=energy(T,C,offset,after,aft,lam);assert (p,q)==(pc,qa);endpoints+=1
    z=Q(reward)+offset[after]-offset[before];lower=Q(0)
    for v,cc,aa in edges:
     z=z/lam-sum((C[before,pp,x]/lam**(2*depth+1) for pp,x in cc),Q(0))+sum((C[after,qq,y]/lam**(2*depth+3) for qq,y in aa),Q(0))
     lower=lower/lam+sum((C[before,pp,x]/lam**(2*depth+1) for pp,x in cc),Q(0))
    z-=sum((lam**(2*depth-len(ct)+k)*C[before,pp,x] for k,(pp,x) in enumerate(ct)),Q(0));z+=sum((lam**(2*depth+2-len(at)+k)*C[after,qq,y] for k,(qq,y) in enumerate(at)),Q(0))
    lower+=sum((lam**(2*depth-len(ct)+k)*C[before,pp,x] for k,(pp,x) in enumerate(ct)),Q(0))
    assert z==(reward+ea-ec)/lam**len(word) and lower==(ec-offset[before])/lam**len(word);identities+=2
 yes=synth(np.zeros((1,2),dtype=np.int16),Q(1),seconds=15,direction=-1,lookahead=4,future_memory=2,depth=depth);no=synth(np.zeros((1,2),dtype=np.int16),Q(1),seconds=15,zero=True,lookahead=4,future_memory=2,depth=depth)
 assert yes.get('exact_rational_graph_certificate') and yes['rational_defect_rate']=='1',yes
 assert no.get('defect_rate')==0,no
 return {'finite_history_double_steps':depth,'future_phase_memory_lengths':[1,2,3],'exhaustive_physical_branch_language_checks':language,'unique_physical_phase_partition_checks':unique,'accepted_shifted_phase_checks':phasechecks,'reader_endpoints':endpoints,'exact_geometric_phase_energy_identities':identities,'positive_control_exact_rational_certificate':True,'zero_energy_negative_control':True,'all_passed':True,'Lean_verified':False}

if __name__=='__main__':
 r={'records':[controls(depth) for depth in [2,3]],'all_passed':True,'Lean_verified':False};(Path(__file__).resolve().parent/'future-history-controls.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print(json.dumps(r,indent=2))
