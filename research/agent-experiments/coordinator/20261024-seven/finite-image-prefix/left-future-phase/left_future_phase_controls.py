"""Exact physical phase assignment and rational phase-energy controls."""
import itertools,json,random
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from left_future_phase_graph import branches,future_word
from left_finite_past_controls import physical,accepted,energy
from left_finite_past_graph import outputs
from left_future_phase_rank import synth

def instrument(T,H,K):
 result=[]
 for before,after,reward,data in branches(T,H,K):
  states,edges,terminals,live=data;lookup={}
  for u,v,cur,aft in edges:
   key=(u,states[v][1][-1]);assert key not in lookup;lookup[key]=(v,cur,aft)
  result.append((before,after,reward,lookup,terminals))
 return result

def path(word,lookup):
 u=0;edges=[]
 for x in word:
  if (u,x) not in lookup:return -1,edges
  e=lookup[u,x];edges.append(e);u=e[0]
 return u,edges

def controls():
 words=[[1]]
 for n in range(2,12):words.extend([1]+list(w)+[1] for w in itertools.product(range(2),repeat=n-2))
 language=unique=phasechecks=0
 for K in [1,2,3]:
  data=instrument(np.zeros((1,2),dtype=np.int16),4,K)
  for word in words:
   counts={r:0 for r in range(5)}
   for before,after,reward,lookup,terminals in data:
    u,_=path(word,lookup);cur,aft=outputs(word) or (None,None)
    w=None if cur is None else future_word(cur,K+1)
    want=cur is not None and accepted(word,before[0],w[0],4) and before[1]==w[:K] and after==(before[0]+1 if w[0] else 0,w[1:])
    assert (u in terminals)==want,(K,before,after,word)
    if want:
     assert future_word(aft,K)==after[1];phasechecks+=1;counts[before[0]]+=1
    language+=1
   for r,count in counts.items():
    cur,aft=outputs(word) or (None,None);b=None if cur is None else physical(cur)[0]
    assert count==int(b is not None and accepted(word,r,b,4))
    unique+=1
 T=np.array([[((p<<1)|x)&7 for x in range(2)] for p in range(8)],dtype=np.int16);data=instrument(T,4,2);phases=sorted({p for a,b,_,_,_ in data for p in [a,b]});rng=random.Random(302055)
 C={(r,p,x):Q(rng.randrange(-9,10)) for r in phases for p in range(8) for x in range(2)};offset={r:Q(rng.randrange(-9,10)) for r in phases};identities=endpoints=0
 for before,after,reward,lookup,terminals in data:
  for word in words:
   u,edges=path(word,lookup)
   if u not in terminals:continue
   cur,aft=outputs(word);p,q,ct,at=terminals[u]
   for lam in [Q(1),Q(3,2),Q(2)]:
    ec,pc=energy(T,C,offset,before,cur,lam);ea,qa=energy(T,C,offset,after,aft,lam);assert (p,q)==(pc,qa);endpoints+=1
    z=Q(reward)+offset[after]-offset[before];lower=Q(0)
    for v,cc,aa in edges:
     z=z/lam-sum((C[before,pp,x]/lam**3 for pp,x in cc),Q(0))+sum((C[after,qq,y]/lam**5 for qq,y in aa),Q(0))
     lower=lower/lam+sum((C[before,pp,x]/lam**3 for pp,x in cc),Q(0))
    z-=sum((lam**(2-len(ct)+k)*C[before,pp,x] for k,(pp,x) in enumerate(ct)),Q(0));z+=sum((lam**(4-len(at)+k)*C[after,qq,y] for k,(qq,y) in enumerate(at)),Q(0))
    lower+=sum((lam**(2-len(ct)+k)*C[before,pp,x] for k,(pp,x) in enumerate(ct)),Q(0))
    assert z==(reward+ea-ec)/lam**len(word) and lower==(ec-offset[before])/lam**len(word);identities+=2
 yes=synth(np.zeros((1,2),dtype=np.int16),Q(1),seconds=15,direction=-1,lookahead=4,future_memory=2);no=synth(np.zeros((1,2),dtype=np.int16),Q(1),seconds=15,zero=True,lookahead=4,future_memory=2)
 assert yes.get('exact_rational_graph_certificate') and yes['rational_defect_rate']=='1',yes
 assert no.get('defect_rate')==0,no
 return {'future_phase_memory_lengths':[1,2,3],'exhaustive_physical_branch_language_checks':language,'unique_physical_phase_partition_checks':unique,'accepted_shifted_phase_checks':phasechecks,'reader_endpoints':endpoints,'exact_geometric_phase_energy_identities':identities,'positive_control_exact_rational_certificate':True,'zero_energy_negative_control':True,'all_passed':True,'Lean_verified':False}

if __name__=='__main__':
 r=controls();(Path(__file__).resolve().parent/'future-phase-controls.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print(json.dumps(r,indent=2))
