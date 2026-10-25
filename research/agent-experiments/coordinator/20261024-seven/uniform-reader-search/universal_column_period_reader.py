"""Synthesize a genuinely uniform spatial-reader certificate by product graphs.

A fixed finite-state signed word energy must increase across each inverse
spatial step by at most C times the newly exposed initial black bit. A second
product graph ensures the initial energy dominates starts of free-zero runs.
All graph constraints cover arbitrary word lengths, not a finite data fit.
Any result still needs exact checking and a Lean proof of the reductions.
"""
import argparse,collections,itertools,time
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
try:
 from core import save
except ModuleNotFoundError:
 import json
 from pathlib import Path
 def save(name,value):
  (Path(__file__).resolve().parent/name).write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')

def synth(T,seconds=15,pattern=(1,)):
 K=len(T);labels=[];idx={};rows=[];rhs=[]
 def var(label):
  if label not in idx:idx[label]=len(labels);labels.append(label)
  return idx[label]
 gamma=var(('gamma',));cost=lambda p,a:var(('cost',p,a));end=lambda p:var(('end',p))
 def add(items,b=0):
  d={}
  for j,v in items:d[j]=d.get(j,0)+v
  rows.append({j:v for j,v in d.items() if v});rhs.append(b)
 spatial_nodes=0;spatial_arcs=0
 for first in range(8):
  initial=(first,int(T[0,first]),0);queue=collections.deque([initial]);seen={initial}
  Z=lambda st:var(('upper',first,*st))
  add([(cost(0,first),1),(Z(initial),-1)])
  while queue:
   st=queue.popleft();last,p,q=st;spatial_nodes+=1
   add([(Z(st),1),(end(p),1),(end(q),-1),(gamma,-(first&1))])
   nextB=(last&1)^(((last>>1)&1)|(last>>2))
   for a,d in itertools.product(range(2),repeat=2):
    token=a+2*nextB+4*d
    output=((token&1)^((last&1)|((last>>1)&1)))+2*(last&1)+4*((last>>1)&1)
    new=(token,int(T[p,token]),int(T[q,output]));spatial_arcs+=1
    add([(Z(st),1),(cost(p,token),1),(cost(q,output),-1),(Z(new),-1)])
    if new not in seen:seen.add(new);queue.append(new)
 Y=lambda st:var(('lower',*st));initial=(0,-1,0);queue=collections.deque([initial]);seen={initial};boundary_arcs=0
 while queue:
  st=queue.popleft();p,last,phase=st
  add([(Y(st),-1),(end(p),-1)])
  firstbits=(0,1) if last==-1 else ((last&1)^(((last>>1)&1)|(last>>2)),)
  for b,d in itertools.product(firstbits,range(2)):
   token=pattern[phase]+2*b+4*d;new=(int(T[p,token]),token,(phase+1)%len(pattern));reward=int(phase==len(pattern)-1);boundary_arcs+=1
   add([(Y(new),1),(Y(st),-1),(cost(p,token),-1)],-reward)
   if new not in seen:seen.add(new);queue.append(new)
 bounds=[(None,None)]*len(labels);bounds[gamma]=(0,None);bounds[end(0)]=(0,0);bounds[Y(initial)]=(0,0)
 ii=[];jj=[];vv=[]
 for i,r in enumerate(rows):
  for j,v in r.items():ii.append(i);jj.append(j);vv.append(v)
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();b=np.array(rhs);objective=np.zeros(len(labels));objective[gamma]=1
 fit=linprog(objective,A_ub=A,b_ub=b,bounds=bounds,method='highs',options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 rec={'reader_states':K,'variables':len(labels),'constraints':len(rows),'spatial_product_nodes':spatial_nodes,'spatial_product_arcs':spatial_arcs,'boundary_product_nodes':len(seen),'boundary_product_arcs':boundary_arcs,'column_period':list(pattern),'solver_status':int(fit.status),'solver_message':fit.message}
 if fit.success:
  rec['gamma']=float(fit.x[gamma]);rec['max_residual']=float(np.max(A@fit.x-b));rec['transition_table']=T.tolist()
  for limit in [100,1000,1000000]:
   f=[Fraction(float(v)).limit_denominator(limit) for v in fit.x]
   if f[gamma]>=0 and f[end(0)]==0 and f[Y(initial)]==0 and all(sum((v*f[j] for j,v in r.items()),Fraction(0))<=bb for r,bb in zip(rows,rhs)):
    rec['exact_rational_graph_certificate']=True;rec['rational_gamma']=str(f[gamma]);rec['certificate']=[{'label':list(l),'value':str(v)} for l,v in zip(labels,f)];break
  if not rec.get('exact_rational_graph_certificate'):rec['numerical_candidate_not_exactly_certified']=True
 return rec

