"""All-radius geometric weighted-reader ranks on complete finite rows.

E(w) = sum_i lambda**i C(q_i,w_i) + lambda**len(w) D(q_end).
C,D >= 0, lambda >= 1. Geometric positional weights permit exponential
rank growth with spatial radius, which additive readers cannot express.
The product-graph potentials propagate with factor lambda. A constant
decrease alpha is paid in the initial potential, before this scaling.
Positive certificates are checked with exact rational arithmetic; the CA
and graph bridges still require Lean proofs before a mathematical claim.
"""
import argparse,hashlib,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save
import universal_folded_row_rank as base

def synth(T,scale=F(2),seconds=10,direction=1,zero=False,badclass=False):
 if badclass:
  from universal_folded_badclass_rank import graph
 else:graph=base.graph
 states,edges,terminals,live=graph(T);labels=[];index={};rows=[]
 def var(l):
  if l not in index:index[l]=len(labels);labels.append(l)
  return index[l]
 alpha=var(('reward_rate',));C=lambda p,x:var(('cost',p,x));D=lambda p:var(('end',p));Z=lambda u:var(('upper',u))
 def add(terms):
  row={}
  for j,v in terms:row[j]=row.get(j,F(0))+v
  rows.append({j:v for j,v in row.items() if v})
 add([(Z(0),1),(alpha,-1)]);add([(Z(0),-1),(alpha,1)])
 for u,v,p,x,out in edges:
  add([(Z(u),1),(C(p,x),-direction),(Z(v),-scale)]+[(C(q,y),direction/scale**2) for q,y in out])
 for u,(p,r,tail) in terminals.items():
  add([(Z(u),1),(D(r),direction*scale**2),(D(p),-direction)]+[(C(q,y),direction*scale**(2-len(tail)+k)) for k,(q,y) in enumerate(tail)])
 bounds=[(None,None)]*len(labels);bounds[alpha]=(0,1)
 for l,j in index.items():
  if l[0] in ['cost','end']:bounds[j]=(0,0) if zero else (0,None)
 ii=[];jj=[];vv=[]
 for i,row in enumerate(rows):
  for j,v in row.items():ii.append(i);jj.append(j);vv.append(float(v))
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();obj=np.zeros(len(labels));obj[alpha]=-1
 fit=linprog(obj,A_ub=A,b_ub=np.zeros(len(rows)),bounds=bounds,method='highs-ipm',options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 r={'reader_states':len(T),'geometric_scale':str(scale),'direction':direction,'eventual_K6_badclass':badclass,'input_radius_unbounded':True,'live_states':len(live),'variables':len(labels),'constraints':len(rows),'solver_status':int(fit.status),'solver_message':fit.message}
 if fit.success:
  r.update({'reward_rate':float(fit.x[alpha]),'maximum_residual':float(np.max(A@fit.x))})
  if fit.x[alpha]>1e-8:
   for den in [100,1000,1000000]:
    vals=[F(float(v)).limit_denominator(den) for v in fit.x]
    if not(0<vals[alpha]<=1):continue
    if any(vals[j]<0 for l,j in index.items() if l[0] in ['cost','end']):continue
    if all(sum((v*vals[j] for j,v in row.items()),F(0))<=0 for row in rows):
     r.update({'exact_rational_graph_certificate':True,'rational_reward_rate':str(vals[alpha]),'transition_table':T.tolist(),'certificate':[{'label':list(l),'value':str(v)} for l,v in zip(labels,vals)]});break
 return r

def validate():
 import itertools,random
 rng=random.Random(302557);T=np.array([[rng.randrange(4) for x in range(4)] for q in range(4)],dtype=np.int16);C=[[rng.randrange(-4,5) for x in range(4)] for q in range(4)];D=[rng.randrange(-4,5) for q in range(4)];n=0
 for scale in [F(1),F(3,2),F(2),F(3)]:
  def energy(word):
   q=0;value=F(0)
   for i,x in enumerate(word):value+=scale**i*C[q][x];q=int(T[q,x])
   return value+scale**len(word)*D[q]
  for N in range(6):
   for tail in itertools.product(range(4),repeat=N):
    if N and not tail[-1]:continue
    word=[3]+list(tail);after=base.updated(word)
    if after is None:continue
    p=q=stage=0;buf=();v=F(1)
    for x in word:
     stage,buf,y=base.advance(stage,buf,x);v=(v-C[p][x])/scale;p=int(T[p,x])
     if y is not None:v+=C[q][y]/scale**3;q=int(T[q,y])
    tailcost=F(0);emitted=[]
    for _ in range(4):
     stage,buf,y=base.advance(stage,buf,0)
     if y is not None:emitted.append((q,y));q=int(T[q,y])
    for k,(r,y) in enumerate(emitted):tailcost+=scale**(2-len(emitted)+k)*C[r][y]
    expected=(1+energy(after)-energy(word))/scale**len(word)
    assert v+tailcost+scale**2*D[q]-D[p]==expected
    n+=1
 T=np.zeros((1,4),dtype=np.int16);pos=synth(T,F(2),direction=-1);neg=synth(T,F(2),zero=True)
 assert pos.get('exact_rational_graph_certificate') and pos['reward_rate']>.99999
 assert neg['solver_status']==0 and abs(neg['reward_rate'])<1e-8
 return {'independent_geometric_path_identities':n,'actual_radius_growth_positive':pos,'zero_energy_negative':neg,'all_passed':True,'Lean_verified':False}

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=180);p.add_argument('--badclass',action='store_true');args=p.parse_args();control=validate();print(control,flush=True);save('folded-geometric-controls.json',control);start=time.monotonic()
 out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'nonnegative_energy_geometric_positional_weights':True,'records':[],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 for scale in [F(3,2),F(2),F(3),F(5,4),F(4)]:
  for kind,T in base.readers():
   begin=time.monotonic();r=synth(T,scale,badclass=args.badclass);r.update({'kind':kind,'seconds':round(time.monotonic()-begin,3)});out['records'].append(r);out['seconds']=round(time.monotonic()-start,3);save('folded-geometric-'+('badclass' if args.badclass else 'all')+'.json',out)
   print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
   if r.get('exact_rational_graph_certificate') or time.monotonic()-start>args.seconds:return
if __name__=='__main__':main()
