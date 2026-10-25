"""Independent finite-past language, full-front, reader and rank controls."""
import itertools,json,random
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from left_finite_past_graph import graph,outputs
from left_lookahead_graph import allowed_word
from left_finite_past_rank import synth

def physical(word):
 # Literal rule table, fixed white wall at the head; keep the new front.
 a=[0]+list(word)+[0,0]
 return [(30>>((a[i+2]<<2)|(a[i+1]<<1)|a[i]))&1 for i in range(len(word)+1)]

def pair(word):return physical(physical(word))

def accepted(word,r,b,H):
 one=physical(word);cur=physical(one);aft=pair(cur)
 return one[0]==int(r>0) and cur[0]==1 and aft[0]==1 and physical(cur)[0]==b and allowed_word(cur,r,H)

def lookup_graph(T,r,b,H):
 states,edges,terminals,live=graph(T,r,b,H);lookup={}
 for u,v,cur,aft in edges:
  x=states[v][1][-1];assert (u,x) not in lookup
  lookup[u,x]=(v,cur,aft)
 return states,lookup,terminals

def path(word,lookup):
 u=0;edges=[]
 for x in word:
  if (u,x) not in lookup:return -1,edges
  edge=lookup[u,x];edges.append(edge);u=edge[0]
 return u,edges

def energy(T,C,H,r,word,lam):
 p=0;value=H[r]
 for i,x in enumerate(word):value+=lam**i*C[r,p,x];p=int(T[p,x])
 return value,p

def controls():
 words=[]
 for m in range(1,12):
  for bits in itertools.product([0,1],repeat=max(0,m-2)):
   words.append([1] if m==1 else [1]+list(bits)+[1])
 physical_checks=0
 for word in words:
  cur=pair(word);aft=pair(cur);got=outputs(word)
  if cur[0] and aft[0]:
   assert got==(cur,aft),(word,got,cur,aft)
   assert len(cur)==len(word)+2 and len(aft)==len(word)+4
  else:assert got is None
  physical_checks+=1
 language=0;positive_paths=0
 for H in [1,2,3,4]:
  for r in range(5):
   for b in range(2):
    if b==0 and r==0 or b==1 and r==4:continue
    _,look,term=lookup_graph(np.zeros((1,2),dtype=np.int16),r,b,H)
    for word in words:
     u,edges=path(word,look);want=accepted(word,r,b,H)
     assert (u in term)==want,(H,r,b,word)
     language+=1;positive_paths+=int(want)
 # A nontrivial reader checks both emitted words, including short inputs.
 T=np.array([[((p<<1)|x)&7 for x in range(2)] for p in range(8)],dtype=np.int16)
 rng=random.Random(301025);C={(r,p,x):Q(rng.randrange(-9,10)) for r in range(5) for p in range(8) for x in range(2)};offset=[Q(rng.randrange(-9,10)) for _ in range(5)]
 identities=readers=0
 for r in range(5):
  for b in range(2):
   if b==0 and r==0 or b==1 and r==4:continue
   states,look,term=lookup_graph(T,r,b,4);future=r+1 if b else 0;reward=0 if b else 4-r
   for word in words:
    u,edges=path(word,look)
    if u not in term:continue
    cur,aft=outputs(word);p,q,ct,at=term[u]
    for lam in [Q(1),Q(3,2),Q(2)]:
     ec,pc=energy(T,C,offset,r,cur,lam);ea,qa=energy(T,C,offset,future,aft,lam)
     assert (p,q)==(pc,qa);readers+=1
     z=Q(reward)+offset[future]-offset[r];lower=Q(0)
     for v,cc,aa in edges:
      z=z/lam-sum((C[r,pp,x]/lam**3 for pp,x in cc),Q(0))+sum((C[future,qq,y]/lam**5 for qq,y in aa),Q(0))
      lower=lower/lam+sum((C[r,pp,x]/lam**3 for pp,x in cc),Q(0))
     z-=sum((lam**(2-len(ct)+k)*C[r,pp,x] for k,(pp,x) in enumerate(ct)),Q(0))
     z+=sum((lam**(4-len(at)+k)*C[future,qq,y] for k,(qq,y) in enumerate(at)),Q(0))
     lower+=sum((lam**(2-len(ct)+k)*C[r,pp,x] for k,(pp,x) in enumerate(ct)),Q(0))
     assert z==(reward+ea-ec)/lam**len(word)
     assert lower==(ec-offset[r])/lam**len(word)
     identities+=2
 calibrations=[]
 for lam in [Q(1),Q(2)]:
  yes=synth(np.zeros((1,2),dtype=np.int16),lam,seconds=15,direction=-1,lookahead=2)
  no=synth(np.zeros((1,2),dtype=np.int16),lam,seconds=15,zero=True,lookahead=2)
  assert yes.get('defect_rate')==1,yes
  if lam==1:assert yes.get('exact_rational_graph_certificate') and yes['rational_defect_rate']=='1',yes
  assert no.get('defect_rate')==0,no
  calibrations.append({'scale':str(lam),'reverse_growth_native_positive':True,'reverse_growth_rational_graph_certificate':yes.get('exact_rational_graph_certificate',False),'zero_energy_defect_rate':no['defect_rate']})
 result={'independent_literal_rule_table_full_front_checks':physical_checks,'exhaustive_finite_predecessor_branch_language_checks':language,'accepted_language_paths':positive_paths,'exhaustive_horizons':[1,2,3,4],'reader_endpoint_checks':readers,'exact_geometric_path_identities':identities,'input_lengths':[1,11],'scales':['1','3/2','2'],'calibrations':calibrations,'all_passed':True,'Lean_verified':False}
 return result

if __name__=='__main__':
 result=controls();(Path(__file__).resolve().parent/'finite-past-controls.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(json.dumps(result,indent=2))
