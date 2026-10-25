"""Sparse Golden defect rank with exact finite past and future lookahead."""
import time
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from left_finite_past_graph import graph

def synth(T,scale=F(1),seconds=60,direction=1,zero=False,lookahead=4):
 labels=[];index={};rows=[];starts=[];arcs=0;nodes=0
 def var(l):
  if l not in index:index[l]=len(labels);labels.append(l)
  return index[l]
 alpha=var(('defect_rate',));C=lambda r,p,x:var(('cost',r,p,x));H=lambda r:var(('phase_offset',r))
 def add(terms):
  row={}
  for j,v in terms:row[j]=row.get(j,F(0))+v
  rows.append({j:v for j,v in row.items() if v})
 for r in range(5):
  for b in [0,1]:
   if b==0 and r==0 or b==1 and r==4:continue
   future=r+1 if b else 0;reward=0 if b else 4-r;states,edges,terminals,live=graph(T,r,b,lookahead);nodes+=len(live);Z=lambda u:var(('upper',r,b,u));L=lambda u:var(('lower',r,b,u))
   initial=[(Z(0),1),(alpha,-reward),(H(future),-direction),(H(r),direction)];add(initial);add([(j,-v) for j,v in initial]);starts.append(L(0))
   for u,v,cur,aft in edges:
    add([(Z(u),1),(Z(v),-scale)]+[(C(r,p,x),-direction/scale**2) for p,x in cur]+[(C(future,q,y),direction/scale**4) for q,y in aft])
    add([(L(v),scale),(L(u),-1)]+[(C(r,p,x),-1/scale**2) for p,x in cur]);arcs+=1
   for u,(p,q,cur,aft) in terminals.items():
    add([(Z(u),1)]+[(C(r,pp,x),-direction*scale**(2-len(cur)+k)) for k,(pp,x) in enumerate(cur)]+[(C(future,qq,y),direction*scale**(4-len(aft)+k)) for k,(qq,y) in enumerate(aft)])
    add([(L(u),-1)]+[(C(r,pp,x),-scale**(2-len(cur)+k)) for k,(pp,x) in enumerate(cur)])
 h0=H(0);bounds=[(None,None)]*len(labels);bounds[alpha]=(0,1);bounds[h0]=(0,0)
 for j in starts:bounds[j]=(None,0)
 if zero:
  for l,j in index.items():
   if l[0]=='cost':bounds[j]=(0,0)
 ii=[];jj=[];vv=[]
 for i,row in enumerate(rows):
  for j,v in row.items():ii.append(i);jj.append(j);vv.append(float(v))
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();objective=np.zeros(len(labels));objective[alpha]=-1
 fit=linprog(objective,A_ub=A,b_ub=np.zeros(len(rows)),bounds=bounds,method='highs-ipm',options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 rec={'reader_states':len(T),'geometric_scale':str(scale),'direction':direction,'explicit_finite_predecessor_witness':True,'current_word_delay':2,'after_word_delay':4,'predecessor_input_flush':8,'current_scored_flush':4,'future_double_steps_checked':lookahead,'uniform_additive_lower_bound_allowed':True,'phase_contexts':5,'variables':len(labels),'constraints':len(rows),'branch_nodes':nodes,'branch_edges':arcs,'solver_status':int(fit.status),'solver_message':fit.message}
 if fit.success:
  rec.update({'defect_rate':float(fit.x[alpha]),'maximum_residual':float(np.max(A@fit.x))})
  if fit.x[alpha]>1e-8:
   for den in [100,1000,1000000]:
    values=[F(float(v)).limit_denominator(den) for v in fit.x]
    if not(0<values[alpha]<=1 and values[h0]==0 and all(values[j]<=0 for j in starts)):continue
    if all(sum((v*values[j] for j,v in row.items()),F(0))<=0 for row in rows):
     rec.update({'exact_rational_graph_certificate':True,'rational_defect_rate':str(values[alpha]),'transition_table':T.tolist(),'certificate':[{'label':list(l),'value':str(v)} for l,v in zip(labels,values)]});break
 return rec
