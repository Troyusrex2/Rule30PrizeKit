"""Nonnegative weighted-DFA ranks on FULL marked finite spatial rows.

The product graph streams the exact two-step CA update, including its four
new edge cells. It accepts canonical finite words with one black marked
center that flips 1->0->1. A positive homogeneous reward rate would give a
nonnegative rank decreasing on every such double step, hence exclude a
finite alternating configuration. No bounded-width training fit is used.
"""
import argparse,collections,hashlib,itertools,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save

def rule(a,b,c):return a^(b|c)
def emit(buffer,x):
 w=buffer+(x,);b=[a&1 for a in w]
 middle=rule(b[1],b[2],b[3]);y=rule(rule(*b[:3]),middle,rule(*b[2:]))
 if w[2]==3:
  if middle!=0 or y!=1:return None
  y+=2
 return w[1:],y

def updated(word):
 buffer=(0,0,0,0);out=[]
 for x in list(word)+[0]*4:
  result=emit(buffer,x)
  if result is None:return None
  buffer,y=result;out.append(y)
 return out

def graph(T):
 initial=((0,0,0,0),0,0,False,False);states=[initial];index={initial:0};queue=collections.deque([initial]);edges=[];terminals={}
 while queue:
  st=queue.popleft();buf,p,q,seen,started=st;u=index[st]
  if started and seen and buf[-1]&1:
   h=buf;r=q;tail=[]
   for _ in range(4):
    result=emit(h,0)
    if result is None:break
    h,y=result;tail.append((r,y));r=int(T[r,y])
   else:terminals[u]=(p,r,tail)
  choices=[0,1] if started else [1]
  if started and not seen:choices.append(3)
  for x in choices:
   if x==3 and not buf[-1]&1:continue
   result=emit(buf,x)
   if result is None:continue
   h,y=result;new=(h,int(T[p,x]),int(T[q,y]),seen or x==3,True)
   if new not in index:index[new]=len(states);states.append(new);queue.append(new)
   edges.append((u,index[new],p,x,q,y))
 # Prefix potentials are required only for prefixes with an accepting
 # continuation. Otherwise an irrelevant positive cycle could forbid a rank.
 reverse=collections.defaultdict(list)
 for u,v,*_ in edges:reverse[v].append(u)
 live=set(terminals);queue=collections.deque(live)
 while queue:
  v=queue.popleft()
  for u in reverse[v]:
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
 for u,v,p,x,q,y in edges:add([(Z(u),1),(C(q,y),direction),(C(p,x),-direction),(Z(v),-1)])
 for u,(p,r,tail) in terminals.items():add([(Z(u),1),(alpha,1),(D(r),direction),(D(p),-direction)]+[(C(q,y),direction) for q,y in tail])
 start=Z(0);bounds=[(None,None)]*len(labels);bounds[alpha]=(0,1);bounds[start]=(0,0)
 for label,j in index.items():
  if label[0] in ['cost','end']:bounds[j]=(0,None)
  if fixed_cost is not None and label[0]=='cost':bounds[j]=(fixed_cost,fixed_cost)
  if fixed_cost is not None and label[0]=='end':bounds[j]=(0,0)
 ii=[];jj=[];vv=[]
 for i,r in enumerate(rows):
  for j,v in r.items():ii.append(i);jj.append(j);vv.append(v)
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();b=np.array(rhs);objective=np.zeros(len(labels));objective[alpha]=-1
 # Exact matrix control: length grows by four. With the reversed drift
 # direction, C=1,D=Z=0 and alpha=1 satisfies every graph inequality.
 if direction==-1:
  control=[1 if l[0] in ['cost','reward_rate'] else 0 for l in labels]
  assert all(sum(v*control[j] for j,v in row.items())<=bb for row,bb in zip(rows,rhs))
 fit=linprog(objective,A_ub=A,b_ub=b,bounds=bounds,method='highs-ipm',options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 rec={'reader_states':len(T),'full_spatial_rows':True,'canonical_marked_center':True,'input_width_unbounded':True,'two_step_update':True,'raw_states':len(states),'live_states':len(live),'edges':len(edges),'accepting_states':len(terminals),'variables':len(labels),'constraints':len(rows),'direction':direction,'solver_status':int(fit.status),'solver_message':fit.message}
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
 yield 'side_of_center',np.array([[0,0,1,1],[1,1,1,1]],dtype=np.int16)
 yield 'last_bit',np.array([[0,1,0,1]]*2,dtype=np.int16)
 for period in [2,4,7]:yield 'spatial_clock'+str(period),np.array([[(p+1)%period]*4 for p in range(period)],dtype=np.int16)
 for depth in [2,3]:yield 'last_bits'+str(depth),np.array([[((p<<1)|(x&1))&((1<<depth)-1) for x in range(4)] for p in range(1<<depth)],dtype=np.int16)
 T=np.array([[2*(p//2 or x>=2)+(x&1) for x in range(4)] for p in range(4)],dtype=np.int16);yield 'side_last_bit',T
 for run in [2,4,7]:yield 'ones_run'+str(run),np.array([[min(run,p+1) if x&1 else 0 for x in range(4)] for p in range(run+1)],dtype=np.int16)

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=165);a=p.parse_args();start=time.monotonic();T=np.zeros((1,4),dtype=np.int16)
 pos=synth(T,direction=-1,fixed_cost=1);neg=synth(T,fixed_cost=0)
 assert pos.get('exact_rational_graph_certificate') and pos['reward_rate']>.999999
 assert neg['solver_status']==0 and abs(neg['reward_rate'])<1e-8
 save('universal-full-row-controls.json',{'length_growth_positive':pos,'zero_energy_negative':neg,'all_passed':True,'Lean_verified':False,'full_problem_solved':False})
 out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'records':[],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 for kind,T in readers():
  begin=time.monotonic();r=synth(T);r.update({'kind':kind,'seconds':round(time.monotonic()-begin,3)});out['records'].append(r);out['seconds']=round(time.monotonic()-start,3);save('universal-full-row-rank.json',out)
  print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
  if r.get('exact_rational_graph_certificate') or time.monotonic()-start>a.seconds:return
if __name__=='__main__':main()
