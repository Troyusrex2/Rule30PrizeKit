"""Direct configured-horizon controls, including actual depth four."""
import json,time,hashlib,sys
from pathlib import Path
from fractions import Fraction as Q
import numpy as np
from left_future_history_graph import branches,groups,future_word
from left_future_history_controls import accepts,physical,path
from left_finite_past_controls import energy

def controls():
 T=np.array([[((p<<1)|x)&7 for x in range(2)] for p in range(8)],dtype=np.int16);language=identities=endpoints=0;started=time.monotonic()
 for depth in [2,3,4]:
  count=0
  for before,after,reward,data in branches(T,13,4,depth):
   states,edges,terminals,live=data;lookup={(u,states[v][0][0][1][-1]):(v,cur,aft) for u,v,cur,aft in edges}
   full=before[1]+(after[1][-1],);allowed=groups(before[0],full[0],13,4,depth)[full]
   phases=[before,after]
   C={(phase,p,x):Q((phase[0]*31+sum(b<<j for j,b in enumerate(phase[1]))*11+p*7+x*3)%19-9) for phase in phases for p in range(8) for x in range(2)}
   H={phase:Q((phase[0]*7+sum(b<<j for j,b in enumerate(phase[1])))%13-6) for phase in phases}
   for prefix in sorted(allowed)[:2]:
    for flip in [-1,1,2*depth+4,len(prefix)-1]:
     word=list(prefix)
     if flip>=0:word[flip]^=1
     while not word[-1]:word.pop()
     u,walk=path(word,lookup);cur=word
     for _ in range(depth):cur=physical(physical(cur))
     aft=physical(physical(cur));want=accepts(word,before[0],full[0],13,depth) and future_word(cur,5)==full
     assert (u in terminals)==want,(depth,before,after,word)
     language+=1;count+=1
     if not want:continue
     assert future_word(aft,4)==after[1]
     p,q,ct,at=terminals[u]
     for lam in [Q(1),Q(3,2),Q(2)]:
      ec,pc=energy(T,C,H,before,cur,lam);ea,qa=energy(T,C,H,after,aft,lam);assert (p,q)==(pc,qa);endpoints+=1
      z=Q(reward)+H[after]-H[before];lower=Q(0)
      for v,cc,aa in walk:
       z=z/lam-sum((C[before,pp,x]/lam**(2*depth+1) for pp,x in cc),Q(0))+sum((C[after,qq,y]/lam**(2*depth+3) for qq,y in aa),Q(0))
       lower=lower/lam+sum((C[before,pp,x]/lam**(2*depth+1) for pp,x in cc),Q(0))
      z-=sum((lam**(2*depth-len(ct)+k)*C[before,pp,x] for k,(pp,x) in enumerate(ct)),Q(0));z+=sum((lam**(2*depth+2-len(at)+k)*C[after,qq,y] for k,(qq,y) in enumerate(at)),Q(0))
      lower+=sum((lam**(2*depth-len(ct)+k)*C[before,pp,x] for k,(pp,x) in enumerate(ct)),Q(0))
      assert z==(reward+ea-ec)/lam**len(word) and lower==(ec-H[before])/lam**len(word);identities+=2
  print({'depth':depth,'horizon':13,'future_phase_bits':4,'configured_language_checks':count,'seconds':round(time.monotonic()-started,3)},flush=True)
 return {'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'finite_history_depths':[2,3,4],'horizon':13,'future_phase_bits':4,'reconstructed_mutated_path_language_checks':language,'reader_endpoints':endpoints,'exact_geometric_energy_identities':identities,'seconds':round(time.monotonic()-started,3),'all_passed':True,'Lean_verified':False}

if __name__=='__main__':
 r=controls();(Path(__file__).resolve().parent/'future-history-extra-controls.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print(json.dumps(r,indent=2))
