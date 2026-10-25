"""Repeat complete-row rank searches on the eventual width-six bad class.

The immutable official K6 certificate has rank zero at 39 of its 64 black
phase strips. Finite Psi would force eventual membership in this class
(Villafuerte/Antigravity, R30-20261025-d1bcba). This is an assumption in
this search, not an unconditional restriction on arbitrary starting rows.
Rank zero is closed under both unknown outer bits, by K6_checkb. No
finite right support is used by the graph. Short words are padded by zero
only when testing their actual finite-row terminal.
"""
import argparse,collections,hashlib,json,re,time
from pathlib import Path
import numpy as np
from core import save
import universal_folded_row_rank as base

REFERENCE=Path(__file__).resolve().parents[2]/'current-reference-3eca-20261024'
K6_SOURCE=REFERENCE/'lean/Ruliology/CellularAutomata/Rule30PeriodTwoWidth6.lean'
RAW=K6_SOURCE.read_bytes()
PACKED=int(re.search(rb'def K6_rankP : Nat := (\d+)',RAW).group(1))
BAD=tuple(s for s in range(64) if (PACKED>>(16*(64+s)))%65536==0)

def rank(phase,s):return (PACKED>>(16*(64*phase+(s&63))))%65536

def graph(T):
 initial=(0,(),0,0,0,0);states=[initial];index={initial:0};queue=collections.deque([initial]);edges=[];terminals={}
 while queue:
  st=queue.popleft();stage,buf,p,q,depth,prefix=st;u=index[st]
  if stage and buf[-1]!=0 and (depth==6 or prefix in BAD):
   ss=stage;h=buf;r=q;tail=[]
   for _ in range(4):
    result=base.advance(ss,h,0)
    if result is None:break
    ss,h,y=result
    if y is not None:tail.append((r,y));r=int(T[r,y])
   else:terminals[u]=(p,r,tail)
  for x in [3] if not stage else range(4):
   result=base.advance(stage,buf,x)
   if result is None:continue
   ss,h,y=result;dd=depth;bb=prefix
   if stage and depth<6:
    bb=prefix+((x>>1)<<depth);dd=depth+1
    if dd==6:
     if bb not in BAD:continue
     bb=0
   rr=q;costs=[]
   if y is not None:costs=[(q,y)];rr=int(T[q,y])
   new=(ss,h,int(T[p,x]),rr,dd,bb)
   if new not in index:index[new]=len(states);states.append(new);queue.append(new)
   edges.append((u,index[new],p,x,costs))
 rev=collections.defaultdict(list)
 for u,v,*_ in edges:rev[v].append(u)
 live=set(terminals);queue=collections.deque(live)
 while queue:
  v=queue.popleft()
  for u in rev[v]:
   if u not in live:live.add(u);queue.append(u)
 assert 0 in live and terminals
 return states,[e for e in edges if e[0] in live and e[1] in live],{u:t for u,t in terminals.items() if u in live},live

def validate():
 import itertools
 count=accepted=0
 for N in range(7):
  for tail in itertools.product(range(4),repeat=N):
   if N and not tail[-1]:continue
   word=[3]+list(tail);r=sum((x>>1)<<i for i,x in enumerate(tail));count+=1
   if base.updated(word) is not None and rank(1,r)==0:
    accepted+=1;r1=((r<<1)|1)^(r|(r>>1));r2=(r1<<1)^(r1|(r1>>1))
    assert rank(0,r1)==rank(1,r2)==0
 T=np.zeros((1,4),dtype=np.int16);states,edges,terminals,live=graph(T)
 transitions={}
 for u,v,p,x,y in edges:transitions[u,x]=v
 paths=0
 for N in range(6):
  for tail in itertools.product(range(4),repeat=N):
   if N and not tail[-1]:continue
   word=[3]+list(tail);r=sum((x>>1)<<i for i,x in enumerate(tail));expected=base.updated(word) is not None and rank(1,r)==0
   u=0
   for x in word:
    u=transitions.get((u,x),-1)
    if u<0:break
   assert (u in terminals)==expected
   paths+=1
 return {'physical_words_checked':count,'accepted_badclass_updates':accepted,'graph_language_paths_checked':paths,'rank_zero_closed_for_physical_steps':True,'all_passed':True,'Lean_verified':False}

def main():
 p=argparse.ArgumentParser();p.add_argument('--peak',action='store_true');p.add_argument('--seconds',type=float,default=180);args=p.parse_args()
 control=validate();save('folded-badclass-controls.json',control);print(control,flush=True)
 base.graph=graph
 if args.peak:
  import universal_folded_prefix_peak as peak
  peak.graph=graph;method=peak.synth;label='prefix-peak'
 else:method=base.synth;label='nonnegative-sum'
 out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'K6_source_sha256':hashlib.sha256(RAW).hexdigest(),'domain':'eventual K6 rank zero at black center phase; finite rows of arbitrary radius','external_reduction':'R30-20261025-d1bcba: Psi_enters_bad_of_finSupp','bad_phase1_strips':list(BAD),'model':label,'records':[],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 start=time.monotonic()
 for kind,T in base.readers():
  begin=time.monotonic();r=method(T);r.update({'kind':kind,'seconds':round(time.monotonic()-begin,3)});out['records'].append(r);out['seconds']=round(time.monotonic()-start,3);save('folded-badclass-'+label+'.json',out)
  print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
  if r.get('exact_rational_graph_certificate') or time.monotonic()-start>args.seconds:return
if __name__=='__main__':main()
