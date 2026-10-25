"""Uniform temporal energies on wider spacetime strips with additive slack.

Every token records M consecutive spatial cells. Its middle M-2 cells
update by Rule 30. Inverse-left reconstruction closes this domain. Boundary
starts after M-3 inverse steps, so the strip reaches the white wall and one
virtual matching column but never assumes an impossible right extension.
Product graphs cover arbitrary temporal lengths. Exact certificates are
discovery objects until CA/graph bridges and inequalities are proved in Lean.
"""
import argparse,collections,functools,hashlib,itertools,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save

FORBIDDEN=[(0,0),(1,1,1,1,1),(0,1,0,1,1,0),(1,0,1,1,0,1,0)]
def legal(ctx):return all(ctx[-len(w):]!=w for w in FORBIDDEN)
def successors(x,M):
 inner=sum((((x>>(j-1))&1)^(((x>>j)&1)|((x>>(j+1))&1)))<<j for j in range(1,M-1))
 return [inner|a|(b<<(M-1)) for a,b in itertools.product((0,1),repeat=2)]
def inverse_token(x,y,M):
 return ((y&1)^((x&1)|((x>>1)&1)))+2*(x&((1<<(M-1))-1))
@functools.lru_cache(None)
def boundary_token(window,M):
 @functools.lru_cache(None)
 def recon(d,t):
  if d==0:return 0
  if d==1:return window[t]
  return recon(d-1,t+1)^(recon(d-1,t)|recon(d-2,t))
 return sum((recon(M-2-j,0) if j<M-1 else window[0])<<j for j in range(M))
def boundary_chunk(history,s,M):
 j=M-3;out=[]
 for b in (1,s):
  window=history+(b,)
  if len(window)==j+1:out.append(boundary_token(window,M))
  history=window[-j:] if j else ()
 return history,out

def synth(M,T,seconds=30,gamma_cap=64,method='highs-ipm'):
 assert M>=3 and T.shape[1]==1<<M
 labels=[];index={};rows=[];rhs=[]
 def var(label):
  if label not in index:index[label]=len(labels);labels.append(label)
  return index[label]
 gamma=var(('gamma',));epsilon=var(('epsilon',));cost=lambda p,a:var(('cost',p,a));end=lambda p:var(('end',p))
 def add(terms,b=0):
  r={}
  for j,v in terms:r[j]=r.get(j,0)+v
  rows.append({j:v for j,v in r.items() if v});rhs.append(b)
 nodes=arcs=0
 for charged in (0,1):
  initial=[(x,int(T[0,x]),0) for x in range(1<<M) if x&1==charged];queue=collections.deque(initial);seen=set(initial)
  Z=lambda st:var(('upper',charged,*st))
  for x,p,q in initial:add([(cost(0,x),1),(Z((x,p,q)),-1)])
  while queue:
   st=queue.popleft();x,p,q=st;nodes+=1
   add([(Z(st),1),(end(p),1),(end(q),-1),(gamma,-charged)])
   for y in successors(x,M):
    out=inverse_token(x,y,M);new=(y,int(T[p,y]),int(T[q,out]));arcs+=1
    add([(Z(st),1),(cost(p,y),1),(cost(q,out),-1),(Z(new),-1)])
    if new not in seen:seen.add(new);queue.append(new)
 Y=lambda st:var(('lower',*st));initial=(0,(),());queue=collections.deque([initial]);seen={initial};boundary_arcs=0
 while queue:
  st=queue.popleft();p,h,ctx=st
  add([(Y(st),-1),(end(p),-1)])
  for s in (0,1):
   word=ctx+(s,)
   if not legal(word):continue
   newh,tokens=boundary_chunk(h,s,M);q=p;terms=[]
   for x in tokens:terms.append((cost(q,x),-1));q=int(T[q,x])
   new=(q,newh,word[-6:]);add([(Y(new),1),(Y(st),-1),(epsilon,-1)]+terms,-(1-s));boundary_arcs+=1
   if new not in seen:seen.add(new);queue.append(new)
 bounds=[(None,None)]*len(labels);bounds[gamma]=(0,gamma_cap);bounds[epsilon]=(0,None);bounds[end(0)]=(0,0);bounds[Y(initial)]=(0,None)
 # Exact independent positive control: V=0, epsilon=1/2, B=1/2.
 # The no00 guard alone bounds zeros by (n+1)/2. A boundary node ending
 # in free0 has Y=0; all other boundary nodes have Y=1/2.
 trivial=[]
 for label in labels:
  v=Fraction(0)
  if label[0]=='epsilon':v=Fraction(1,2)
  elif label[0]=='lower':v=Fraction(1,2) if not label[-1] or label[-1][-1]==1 else Fraction(0)
  trivial.append(v)
 assert all(sum((v*trivial[j] for j,v in r.items()),Fraction(0))<=b for r,b in zip(rows,rhs))
 ii=[];jj=[];vv=[]
 for i,r in enumerate(rows):
  for j,v in r.items():ii.append(i);jj.append(j);vv.append(v)
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();b=np.array(rhs);objective=np.zeros(len(labels));objective[epsilon]=1
 fit=linprog(objective,A_ub=A,b_ub=b,bounds=bounds,method=method,options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 r={'strip_width':M,'reader_states':len(T),'alphabet_size':1<<M,'boundary_inverse_steps':M-3,'variables':len(labels),'constraints':len(rows),'spatial_nodes':nodes,'spatial_arcs':arcs,'boundary_nodes':len(seen),'boundary_arcs':boundary_arcs,'additive_boundary_slack_allowed':True,'exact_half_density_control_passed':True,'gamma_cap':gamma_cap,'solver_status':int(fit.status),'solver_message':fit.message}
 if fit.success:
  r.update({'epsilon':float(fit.x[epsilon]),'gamma':float(fit.x[gamma]),'additive_slack':float(fit.x[Y(initial)]),'maximum_residual':float(np.max(A@fit.x-b)),'transition_table':T.tolist()})
  for denominator in [100,1000,1000000]:
   f=[Fraction(float(v)).limit_denominator(denominator) for v in fit.x]
   if not(0<=f[gamma]<=gamma_cap and f[epsilon]>=0 and f[end(0)]==0 and f[Y(initial)]>=0):continue
   if all(sum((v*f[j] for j,v in rr.items()),Fraction(0))<=bound for rr,bound in zip(rows,rhs)):
    r.update({'exact_rational_graph_certificate':True,'rational_epsilon':str(f[epsilon]),'rational_gamma':str(f[gamma]),'rational_additive_slack':str(f[Y(initial)]),'useful_critical_candidate':f[epsilon]<=Fraction(1,5),'certificate':[{'label':list(l),'value':str(v)} for l,v in zip(labels,f)]});break
 return r

def main():
 p=argparse.ArgumentParser();p.add_argument('--max-width',type=int,default=8);p.add_argument('--seconds',type=float,default=165);a=p.parse_args();start=time.monotonic();records=[]
 for M in range(3,a.max_width+1):
  for kind,T in [('constant',np.zeros((1,1<<M),dtype=np.int16)),('nonempty',np.ones((2,1<<M),dtype=np.int16))]:
   begin=time.monotonic();r=synth(M,T);r.update({'kind':kind,'seconds':round(time.monotonic()-begin,3)})
   if not r.get('useful_critical_candidate'):r.pop('certificate',None)
   records.append(r);save('universal-strip-energy.json',{'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'arbitrary_lengths_encoded_by_product_graphs':True,'records':records,'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)})
   print({k:v for k,v in r.items() if k not in ['transition_table','certificate']},flush=True)
   if r.get('useful_critical_candidate') or time.monotonic()-start>a.seconds:return
if __name__=='__main__':main()
