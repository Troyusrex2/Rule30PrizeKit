"""Sparse Golden defect rank with exact finite past and future lookahead."""
import time,sys
from pathlib import Path
for _p in [Path("D:/MWB/Rule30/toolchain/exact-lp-research"),Path.home()/"Rule30-offload/_cache/exact-lp-research"]:
 if _p.is_dir():sys.path.insert(0,str(_p))
import z3
from fractions import Fraction as F
import numpy as np
from left_finite_history_graph import graph

def synth(T,scale=F(1),seconds=60,direction=1,zero=False,lookahead=4,depth=2):
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
   future=r+1 if b else 0;reward=0 if b else 4-r;states,edges,terminals,live=graph(T,r,b,lookahead,depth);nodes+=len(live);Z=lambda u:var(('upper',r,b,u));L=lambda u:var(('lower',r,b,u))
   initial=[(Z(0),1),(alpha,-reward),(H(future),-direction),(H(r),direction)];add(initial);add([(j,-v) for j,v in initial]);starts.append(L(0))
   for u,v,cur,aft in edges:
    add([(Z(u),1),(Z(v),-scale)]+[(C(r,p,x),-direction/scale**(2*depth)) for p,x in cur]+[(C(future,q,y),direction/scale**(2*depth+2)) for q,y in aft])
    add([(L(v),scale),(L(u),-1)]+[(C(r,p,x),-1/scale**(2*depth)) for p,x in cur]);arcs+=1
   for u,(p,q,cur,aft) in terminals.items():
    add([(Z(u),1)]+[(C(r,pp,x),-direction*scale**(2*depth-len(cur)+k)) for k,(pp,x) in enumerate(cur)]+[(C(future,qq,y),direction*scale**(2*depth+2-len(aft)+k)) for k,(qq,y) in enumerate(aft)])
    add([(L(u),-1)]+[(C(r,pp,x),-scale**(2*depth-len(cur)+k)) for k,(pp,x) in enumerate(cur)])
 h0=H(0);bounds=[(None,None)]*len(labels);bounds[alpha]=(0,1);bounds[h0]=(0,0)
 for j in starts:bounds[j]=(None,0)
 if zero:
  for l,j in index.items():
   if l[0]=='cost':bounds[j]=(0,0)

 bounds[alpha]=(1,1)
 xs=[z3.Real('v'+str(j)) for j in range(len(labels))]
 solver=z3.SolverFor('QF_LRA');solver.set(timeout=int(seconds*1000))
 def val(q):return z3.RealVal(str(q.numerator)+'/'+str(q.denominator)) if isinstance(q,F) else z3.RealVal(q)
 for row in rows:solver.add(z3.Sum([val(v)*xs[j] for j,v in row.items()])<=0)
 for x,(lo,hi) in zip(xs,bounds):
  if lo is not None:solver.add(x>=val(lo))
  if hi is not None:solver.add(x<=val(hi))
 started=time.monotonic();answer=solver.check()
 rec={'finite_history_double_steps':depth,'reader_states':len(T),'geometric_scale':str(scale),'direction':direction,'explicit_finite_predecessor_witness':True,'future_double_steps_checked':lookahead,'fixed_positive_defect_rate':1,'signed_costs':True,'uniform_additive_lower_bound_allowed':True,'variables':len(labels),'constraints':len(rows),'branch_nodes':nodes,'branch_edges':arcs,'exact_solver':'Z3 '+z3.get_version_string(),'solver_outcome':str(answer),'solver_seconds':round(time.monotonic()-started,3),'Lean_verified':False}
 if answer==z3.unknown:rec['reason_unknown']=solver.reason_unknown()
 if answer==z3.sat:
  model=solver.model();values=[]
  for x in xs:
   v=model.eval(x,model_completion=True);assert z3.is_rational_value(v);values.append(F(v.numerator_as_long(),v.denominator_as_long()))
  assert values[alpha]==1 and all(sum((v*values[j] for j,v in row.items()),F(0))<=0 for row in rows)
  assert all((lo is None or lo<=v) and (hi is None or v<=hi) for v,(lo,hi) in zip(values,bounds))
  rec.update({'exact_rational_graph_certificate':True,'transition_table':T.tolist(),'certificate':[{'label':list(l),'value':str(v)} for l,v in zip(labels,values)]})
 return rec
