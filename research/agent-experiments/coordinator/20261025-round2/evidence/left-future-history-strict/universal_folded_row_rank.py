"""Full finite configurations read jointly from the center toward both ends.

Token d has left cell -d in bit0 and right cell +d in bit1. Token0 is3;
the last token is nonzero. This retains the entire interval between moving
ends and anchors prefix costs at the constrained center, not the outer edge.
The exact radius-two transducer accepts 1->0->1 center double steps. A
positive all-length nonnegative rank certificate would imply CQ01 after
formal bridges; numerical fitting alone is never accepted as a proof.
"""
import argparse,collections,hashlib,itertools,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save

def rule(a,b,c):return a^(b|c)
def two(bits):return rule(rule(*bits[:3]),rule(*bits[1:4]),rule(*bits[2:]))
def swap(x):return (x>>1)+2*(x&1)
def pair_emit(window):
 return two([(x&1) for x in reversed(window)])+2*two([x>>1 for x in window])
def advance(stage,buffer,x):
 if stage==0:
  if x!=3:return None
  return 1,(3,),None
 if stage==1:return 2,buffer+(x,),None
 if stage==2:
  window=(swap(x),swap(buffer[1]),3,buffer[1],x);out=pair_emit(window)
  if not buffer[1]&1 or out!=3:return None
  return 3,window[1:],out
 window=buffer+(x,);return 3,window[1:],pair_emit(window)

def updated(word):
 stage=0;buf=();out=[]
 for x in list(word)+[0]*4:
  r=advance(stage,buf,x)
  if r is None:return None
  stage,buf,y=r
  if y is not None:out.append(y)
 return out

def graph(T):
 initial=(0,(),0,0);states=[initial];index={initial:0};queue=collections.deque([initial]);edges=[];terminals={}
 while queue:
  st=queue.popleft();stage,buf,p,q=st;u=index[st]
  if stage and buf[-1]!=0:
   ss=stage;h=buf;r=q;tail=[]
   for _ in range(4):
    result=advance(ss,h,0)
    if result is None:break
    ss,h,y=result
    if y is not None:tail.append((r,y));r=int(T[r,y])
   else:terminals[u]=(p,r,tail)
  for x in [3] if not stage else range(4):
   result=advance(stage,buf,x)
   if result is None:continue
   ss,h,y=result;rr=q;costs=[]
   if y is not None:costs=[(q,y)];rr=int(T[q,y])
   new=(ss,h,int(T[p,x]),rr)
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

def synth(T,seconds=20,direction=1,fixed_cost=None):
 states,edges,terminals,live=graph(T);labels=[];index={};rows=[];rhs=[]
 def var(label):
  if label not in index:index[label]=len(labels);labels.append(label)
  return index[label]
 alpha=var(('reward_rate',));C=lambda p,a:var(('cost',p,a));D=lambda p:var(('end',p));Z=lambda u:var(('upper',u))
 def add(terms,b=0):
  r={}
  for j,v in terms:r[j]=r.get(j,0)+v
  rows.append({j:v for j,v in r.items() if v});rhs.append(b)
 for u,v,p,x,emitted in edges:add([(Z(u),1),(C(p,x),-direction),(Z(v),-1)]+[(C(q,y),direction) for q,y in emitted])
 for u,(p,r,tail) in terminals.items():add([(Z(u),1),(alpha,1),(D(r),direction),(D(p),-direction)]+[(C(q,y),direction) for q,y in tail])
 start=Z(0);bounds=[(None,None)]*len(labels);bounds[alpha]=(0,1);bounds[start]=(0,0)
 for label,j in index.items():
  if label[0] in ['cost','end']:bounds[j]=(0,None)
  if fixed_cost is not None and label[0]=='cost':bounds[j]=(fixed_cost,fixed_cost)
  if fixed_cost is not None and label[0]=='end':bounds[j]=(0,0)
 if direction==-1:
  control=[1 if l[0] in ['cost','reward_rate'] else min(2,states[l[1]][0]) if l[0]=='upper' else 0 for l in labels]
  assert all(sum(v*control[j] for j,v in row.items())<=bb for row,bb in zip(rows,rhs))
 ii=[];jj=[];vv=[]
 for i,r in enumerate(rows):
  for j,v in r.items():ii.append(i);jj.append(j);vv.append(v)
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();b=np.array(rhs);objective=np.zeros(len(labels));objective[alpha]=-1
 fit=linprog(objective,A_ub=A,b_ub=b,bounds=bounds,method='highs-ipm',options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 rec={'reader_states':len(T),'full_spatial_rows':True,'center_out_folded_pairs':True,'input_radius_unbounded':True,'two_step_update':True,'raw_states':len(states),'live_states':len(live),'edges':len(edges),'accepting_states':len(terminals),'variables':len(labels),'constraints':len(rows),'direction':direction,'solver_status':int(fit.status),'solver_message':fit.message}
 if fit.success:
  rec.update({'reward_rate':float(fit.x[alpha]),'maximum_residual':float(np.max(A@fit.x-b)),'transition_table':T.tolist()})
  if fit.x[alpha]>1e-8:
   for denominator in [100,1000,1000000]:
    f=[Fraction(float(v)).limit_denominator(denominator) for v in fit.x]
    if not(0<f[alpha]<=1 and f[start]==0):continue
    if any(f[j]<0 for label,j in index.items() if label[0] in ['cost','end']):continue
    if all(sum((v*f[j] for j,v in row.items()),Fraction(0))<=bb for row,bb in zip(rows,rhs)):
     rec.update({'exact_rational_graph_certificate':True,'rational_reward_rate':str(f[alpha]),'certificate':[{'label':list(l),'value':str(v)} for l,v in zip(labels,f)]});break
 return rec

def readers():
 yield 'constant',np.zeros((1,4),dtype=np.int16)
 yield 'transient',np.ones((2,4),dtype=np.int16)
 yield 'last_pair',np.tile(np.arange(4),(4,1)).astype(np.int16)
 for period in [2,4,7]:yield 'radial_clock'+str(period),np.array([[(p+1)%period]*4 for p in range(period)],dtype=np.int16)
 for plane in [1,2,3]:
  for length in [1,2,4]:
   T=np.full((length+2,4),length+1,dtype=np.int16)
   for p in range(length+1):
    for x in range(4):
     if x&plane==plane:T[p,x]=(p+1)%(length+1)
   yield 'black_prefix_plane'+str(plane)+'_'+str(length),T
 for depth in [2,3]:
  yield 'left_last_bits'+str(depth),np.array([[((p<<1)|(x&1))&((1<<depth)-1) for x in range(4)] for p in range(1<<depth)],dtype=np.int16)
  yield 'right_last_bits'+str(depth),np.array([[((p<<1)|(x>>1))&((1<<depth)-1) for x in range(4)] for p in range(1<<depth)],dtype=np.int16)

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=165);a=p.parse_args();start=time.monotonic();T=np.zeros((1,4),dtype=np.int16)
 pos=synth(T,direction=-1,fixed_cost=1);neg=synth(T,fixed_cost=0)
 assert pos.get('exact_rational_graph_certificate') and pos['reward_rate']>.999999
 assert neg['solver_status']==0 and abs(neg['reward_rate'])<1e-8
 save('universal-folded-row-controls.json',{'length_growth_positive':pos,'zero_energy_negative':neg,'all_passed':True,'Lean_verified':False,'full_problem_solved':False})
 out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'records':[],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 for kind,T in readers():
  begin=time.monotonic();r=synth(T);r.update({'kind':kind,'seconds':round(time.monotonic()-begin,3)});out['records'].append(r);out['seconds']=round(time.monotonic()-start,3);save('universal-folded-row-rank.json',out)
  print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
  if r.get('exact_rational_graph_certificate') or time.monotonic()-start>a.seconds:return
if __name__=='__main__':main()
