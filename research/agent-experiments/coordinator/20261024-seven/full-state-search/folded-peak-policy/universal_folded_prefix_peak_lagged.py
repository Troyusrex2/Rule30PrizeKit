"""Signed prefix-peak ranks on full center-out configurations.

Energy is max(0, all signed prefix scores), hence nonnegative without
requiring nonnegative transition costs. The product graph imposes a
SUFFICIENT prefix simulation: each emitted after-prefix score is below the
current before-prefix score by alpha. Failure does not exclude other
prefix-peak simulation strategies. Exact positive candidates still need
Lean proofs of graph, prefix-maximum and Rule30 bridges.
"""
import argparse,hashlib,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save
from universal_folded_row_rank import graph,readers

def post_states(T):
 found={int(T[0,3])};stack=list(found)
 while stack:
  p=stack.pop()
  for x in range(4):
   q=int(T[p,x])
   if q not in found:found.add(q);stack.append(q)
 return found

def suffix_paths(T,current,buffer,length,post):
 if length==0:return [[]]
 assert length<=len(buffer)
 answer=[]
 for p in sorted(post):
  state=p;path=[]
  for x in buffer[-length:]:path.append((state,x));state=int(T[state,x])
  if state==current:answer.append(path)
 assert answer
 return answer

def synth(T,seconds=15,toy=False,fixed_zero=False,offset=2):
 if toy:
  states=[(0,(),0,0),(1,(3,),0,0),(3,(),0,0)]
  edges=[(0,1,0,3,[]),(1,2,0,1,[(0,3)])];terminals={2:(0,0,[])};live={0,1,2}
 else:states,edges,terminals,live=graph(T)
 post=post_states(T);labels=[];index={};rows=[];rhs=[]
 def var(label):
  if label not in index:index[label]=len(labels);labels.append(label)
  return index[label]
 alpha=var(('reward_rate',));C=lambda p,a:var(('cost',p,a));Z=lambda u:var(('upper',u))
 def add(terms):
  row={}
  for j,v in terms:row[j]=row.get(j,0)+v
  rows.append({j:v for j,v in row.items() if v});rhs.append(0)
 add([(alpha,1),(C(0,3),-1)])
 for u,v,p,x,emitted in edges:add([(Z(u),1),(C(p,x),-1),(Z(v),-1)]+[(C(q,y),1) for q,y in emitted])
 for u in sorted(live):
  if states[u][0]==3:
   for path in suffix_paths(T,states[u][2],states[u][1],2-offset,post):
    add([(Z(u),1),(alpha,1)]+[(C(p,x),1) for p,x in path])
 for u,(p,r,tail) in terminals.items():
  partial=[]
  if not tail:add([(Z(u),1),(alpha,1)])
  for k,(q,y) in enumerate(tail,1):
   partial.append((C(q,y),1))
   for path in suffix_paths(T,p,states[u][1],max(0,2-k-offset),post):
    add([(Z(u),1),(alpha,1)]+partial+[(C(pp,x),1) for pp,x in path])
 start=Z(0);bounds=[(None,None)]*len(labels);bounds[alpha]=(0,1);bounds[start]=(0,0)
 if fixed_zero:
  for label,j in index.items():
   if label[0]=='cost':bounds[j]=(0,0)
 if toy:
  control=[1 if l[0] in ['reward_rate','cost'] else 0 if l[1]==0 else -1 for l in labels]
  assert all(sum(v*control[j] for j,v in row.items())<=0 for row in rows)
 ii=[];jj=[];vv=[]
 for i,row in enumerate(rows):
  for j,v in row.items():ii.append(i);jj.append(j);vv.append(v)
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();b=np.array(rhs);objective=np.zeros(len(labels));objective[alpha]=-1
 fit=linprog(objective,A_ub=A,b_ub=b,bounds=bounds,method='highs-ipm',options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 r={'reader_states':len(T),'signed_prefix_peak_energy':True,'prefix_match_offset':offset,'all_consistent_reader_preimages_checked':True,'nonnegative_by_prefix_maximum':True,'simulation_is_sufficient_not_necessary':True,'toy_prefix_deletion_not_Rule30':toy,'live_states':len(live),'variables':len(labels),'constraints':len(rows),'solver_status':int(fit.status),'solver_message':fit.message}
 if fit.success:
  r.update({'reward_rate':float(fit.x[alpha]),'maximum_residual':float(np.max(A@fit.x-b)),'transition_table':T.tolist()})
  if fit.x[alpha]>1e-8:
   for denominator in [100,1000,1000000]:
    f=[Fraction(float(v)).limit_denominator(denominator) for v in fit.x]
    if not(0<f[alpha]<=1 and f[start]==0):continue
    if all(sum((v*f[j] for j,v in row.items()),Fraction(0))<=0 for row in rows):
     r.update({'exact_rational_graph_certificate':True,'rational_reward_rate':str(f[alpha]),'certificate':[{'label':list(l),'value':str(v)} for l,v in zip(labels,f)]});break
 return r

def transient(T):
 k=len(T);U=np.empty((k+1,4),dtype=np.int16);U[0]=1+T[0];U[1:]=1+T;return U

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=165);a=p.parse_args();start=time.monotonic();base=np.zeros((1,4),dtype=np.int16)
 pos=synth(base,toy=True);neg=[synth(base,fixed_zero=True,offset=h) for h in [0,1,2]]
 assert pos.get('exact_rational_graph_certificate') and pos['reward_rate']>.999999
 assert all(r['solver_status']==0 and abs(r['reward_rate'])<1e-8 for r in neg)
 save('folded-prefix-peak-lagged-controls.json',{'toy_deletion_positive':pos,'zero_energy_negative_offsets':neg,'all_passed':True,'Lean_verified':False,'full_problem_solved':False})
 records=[]
 for offset in [0,1,2]:
  for kind,T in readers():
   begin=time.monotonic();r=synth(transient(T),offset=offset);r.update({'kind':'transient_'+kind,'seconds':round(time.monotonic()-begin,3)});records.append(r)
   save('universal-folded-prefix-peak-lagged.json',{'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'graph_helper_sha256':hashlib.sha256((Path(__file__).resolve().parent/'universal_folded_row_rank.py').read_bytes()).hexdigest(),'records':records,'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)})
   print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
   if r.get('exact_rational_graph_certificate') or time.monotonic()-start>a.seconds:return
if __name__=='__main__':main()
