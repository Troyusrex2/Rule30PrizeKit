"""Signed geometric energy, nonnegative on the whole accepted row language.

Local costs and terminal values may now be negative. A separate lower
potential proves E(w)>=0 for every accepted canonical finite input word,
of arbitrary radius. In a hypothetical infinite alternating finite-row
trajectory, every successive row belongs to this domain. Constant strict
decrease would contradict this lower bound. This is a sufficient graph
certificate; CA/domain/energy bridges still need formalization in Lean.
"""
import argparse,hashlib,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save
import universal_folded_row_rank as base

def synth(T,scale=F(1),seconds=15,direction=1,zero=False,badclass=True):
 if badclass:
  from universal_folded_badclass_rank import graph
 else:graph=base.graph
 states,edges,terminals,live=graph(T);labels=[];index={};rows=[]
 def var(l):
  if l not in index:index[l]=len(labels);labels.append(l)
  return index[l]
 alpha=var(('reward_rate',));C=lambda p,x:var(('cost',p,x));D=lambda p:var(('end',p));Z=lambda u:var(('upper',u));L=lambda u:var(('lower',u))
 def add(terms):
  row={}
  for j,v in terms:row[j]=row.get(j,F(0))+v
  rows.append({j:v for j,v in row.items() if v})
 add([(Z(0),1),(alpha,-1)]);add([(Z(0),-1),(alpha,1)])
 for u,v,p,x,out in edges:
  add([(Z(u),1),(C(p,x),-direction),(Z(v),-scale)]+[(C(q,y),direction/scale**2) for q,y in out])
  add([(L(v),scale),(L(u),-1),(C(p,x),-1)])
 for u,(p,r,tail) in terminals.items():
  add([(Z(u),1),(D(r),direction*scale**2),(D(p),-direction)]+[(C(q,y),direction*scale**(2-len(tail)+k)) for k,(q,y) in enumerate(tail)])
  add([(L(u),-1),(D(p),-1)])
 lower0=L(0);bounds=[(None,None)]*len(labels);bounds[alpha]=(0,1);bounds[lower0]=(0,0)
 if zero:
  for l,j in index.items():
   if l[0] in ['cost','end']:bounds[j]=(0,0)
 ii=[];jj=[];vv=[]
 for i,row in enumerate(rows):
  for j,v in row.items():ii.append(i);jj.append(j);vv.append(float(v))
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();obj=np.zeros(len(labels));obj[alpha]=-1
 fit=linprog(obj,A_ub=A,b_ub=np.zeros(len(rows)),bounds=bounds,method='highs-ipm',options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 r={'reader_states':len(T),'geometric_scale':str(scale),'direction':direction,'eventual_K6_badclass':badclass,'signed_costs_and_end_values':True,'global_nonnegativity_on_accepted_language':True,'input_radius_unbounded':True,'live_states':len(live),'variables':len(labels),'constraints':len(rows),'solver_status':int(fit.status),'solver_message':fit.message}
 if fit.success:
  r.update({'reward_rate':float(fit.x[alpha]),'maximum_residual':float(np.max(A@fit.x))})
  if fit.x[alpha]>1e-8:
   for den in [100,1000,1000000]:
    vals=[F(float(v)).limit_denominator(den) for v in fit.x]
    if not(0<vals[alpha]<=1 and vals[lower0]==0):continue
    if all(sum((v*vals[j] for j,v in row.items()),F(0))<=0 for row in rows):
     r.update({'exact_rational_graph_certificate':True,'rational_reward_rate':str(vals[alpha]),'transition_table':T.tolist(),'certificate':[{'label':list(l),'value':str(v)} for l,v in zip(labels,vals)]});break
 return r

def readers():
 yield from base.readers()
 for length in [2,3]:
  count=4**length;T=np.array([[((p<<2)|x)&(count-1) for x in range(4)] for p in range(count)],dtype=np.int16)
  yield 'joint_last_pairs'+str(length),T

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=180);args=p.parse_args();T=np.zeros((1,4),dtype=np.int16)
 pos=synth(T,F(2),direction=-1);neg=synth(T,F(2),zero=True)
 assert pos.get('exact_rational_graph_certificate') and pos['reward_rate']>.99999
 assert neg['solver_status']==0 and abs(neg['reward_rate'])<1e-8
 save('folded-signed-geometric-controls.json',{'actual_radius_growth_positive':pos,'zero_energy_negative':neg,'all_passed':True,'Lean_verified':False});start=time.monotonic()
 out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'records':[],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 for scale in [F(1),F(2),F(3,2),F(3)]:
  for kind,T in readers():
   begin=time.monotonic();r=synth(T,scale);r.update({'kind':kind,'seconds':round(time.monotonic()-begin,3)});out['records'].append(r);out['seconds']=round(time.monotonic()-start,3);save('folded-signed-geometric.json',out)
   print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
   if r.get('exact_rational_graph_certificate') or time.monotonic()-start>args.seconds:return
if __name__=='__main__':main()
