"""Relax full-state ranks to pay only verified Golden defect increments.

The context r=0..4 counts preceding free ones. A free zero pays 4-r;
free ones pay zero. Legal contexts exclude free00 and free11111. A rank
may remain flat throughout a perfect 01111 cycle. The checked quantitative
drift theorem forces infinitely many positive defects in a hypothetical
finite counterexample, so bounded-below energy and defect decrease would
still suffice. All CA, context, and potential bridges remain to formalize.
"""
import argparse,collections,hashlib,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save
from left_lookahead_graph import graph as original_graph
from universal_folded_row_rank import readers,updated,advance

def branch(data,b):
 states,edges,terminals,live=data
 edges=[e for e in edges if states[e[0]][0]!=1 or 1-e[3]==b]
 successors=collections.defaultdict(list);reverse=collections.defaultdict(list)
 for u,v,*_ in edges:successors[u].append(v);reverse[v].append(u)
 reachable={0};queue=collections.deque([0])
 while queue:
  for v in successors[queue.popleft()]:
   if v not in reachable:reachable.add(v);queue.append(v)
 terminals={u:t for u,t in terminals.items() if u in reachable and (b==1 or states[u][0]>=2)}
 live=set(terminals);queue=collections.deque(live)
 while queue:
  for u in reverse[queue.popleft()]:
   if u in reachable and u not in live:live.add(u);queue.append(u)
 assert 0 in live
 return states,[e for e in edges if e[0] in live and e[1] in live],terminals,live

def synth(T,scale=F(1),seconds=15,direction=1,zero=False,lookahead=4):
 branches={}
 for context in range(5):
  raw=original_graph(T,context,lookahead)
  for bit in [0,1]:
   if bit==0 and context==0 or bit==1 and context==4:continue
   branches[context,bit]=branch(raw,bit)
 labels=[];index={};rows=[];arcs=0
 def var(l):
  if l not in index:index[l]=len(labels);labels.append(l)
  return index[l]
 alpha=var(('defect_rate',));C=lambda r,p,x:var(('cost',r,p,x));H=lambda r:var(('phase_offset',r))
 def add(terms):
  row={}
  for j,v in terms:row[j]=row.get(j,F(0))+v
  rows.append({j:v for j,v in row.items() if v})
 starts=[]
 for r in range(5):
  for b in [0,1]:
   if b==0 and r==0 or b==1 and r==4:continue
   future=r+1 if b else 0;reward=0 if b else 4-r;states,edges,terminals,live=branches[r,b];Z=lambda u:var(('upper',r,b,u));L=lambda u:var(('lower',r,b,u))
   terms=[(Z(0),1),(alpha,-reward),(H(future),-direction),(H(r),direction)];add(terms);add([(j,-v) for j,v in terms]);starts.append(L(0))
   for u,v,p,x,out in edges:
    add([(Z(u),1),(C(r,p,x),-direction),(Z(v),-scale)]+[(C(future,q,y),direction/scale**2) for q,y in out])
    add([(L(v),scale),(L(u),-1),(C(r,p,x),-1)]);arcs+=1
   for u,(p,q,tail) in terminals.items():
    add([(Z(u),1)]+[(C(future,rr,y),direction*scale**(2-len(tail)+k)) for k,(rr,y) in enumerate(tail)])
    add([(L(u),-1)])
 phase0=H(0);bounds=[(None,None)]*len(labels);bounds[alpha]=(0,1);bounds[phase0]=(0,0)
 for j in starts:bounds[j]=(None,0)
 if zero:
  for l,j in index.items():
   if l[0]=='cost':bounds[j]=(0,0)
 ii=[];jj=[];vv=[]
 for i,row in enumerate(rows):
  for j,v in row.items():ii.append(i);jj.append(j);vv.append(float(v))
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();objective=np.zeros(len(labels));objective[alpha]=-1
 fit=linprog(objective,A_ub=A,b_ub=np.zeros(len(rows)),bounds=bounds,method='highs-ipm',options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 rec={'reader_states':len(T),'geometric_scale':str(scale),'direction':direction,'positive_reward_only_for_short_Golden_gaps':True,'finite_contexts':5,'actual_context_branches':8,'eventual_K6_rank_zero':False,'finite_left_white_wall_domain':True,'eventual_width_six_free_language':True,'future_double_steps_checked':lookahead,'left_head_black_before_and_after':True,'uniform_additive_lower_bound_allowed':True,'variables':len(labels),'constraints':len(rows),'branch_edges':arcs,'solver_status':int(fit.status),'solver_message':fit.message}
 if fit.success:
  rec.update({'defect_rate':float(fit.x[alpha]),'maximum_residual':float(np.max(A@fit.x))})
  if fit.x[alpha]>1e-8:
   for den in [100,1000,1000000]:
    values=[F(float(v)).limit_denominator(den) for v in fit.x]
    if not(0<values[alpha]<=1 and values[phase0]==0 and all(values[j]<=0 for j in starts)):continue
    if all(sum((v*values[j] for j,v in row.items()),F(0))<=0 for row in rows):
     rec.update({'exact_rational_graph_certificate':True,'rational_defect_rate':str(values[alpha]),'transition_table':T.tolist(),'certificate':[{'label':list(l),'value':str(v)} for l,v in zip(labels,values)]});break
 return rec

