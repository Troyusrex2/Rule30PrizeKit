"""Universal column-flux synthesis with a constrained boundary language.

The earlier finite fits charged one spatial black cell per free zero-run
on an unrestricted boundary. That unit-coefficient target has a checked
counterexample. Here the spatial coefficient is explicit, boundary domains
are selectable, and finite graph potentials certify ALL column lengths.
Numerical fits remain conjectural until the CA bridge and certificate are
replayed in Lean. Positive candidates are checked in rational arithmetic.
"""
import collections,itertools,time
from fractions import Fraction as Q
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

def valid(a,b,columns):
 if columns==2:return not(a>>1) or (a&1)!=(b>>1)
 return ((b>>1)&1)==((a&1)^(((a>>1)&1)|(a>>2)))

def emit(a,b,columns):
 return ((b&1)^((a&1)|((a>>1)&1)))+2*(a&1)+(4*((a>>1)&1) if columns==3 else 0)

def reader(columns,memory,clock=1):
 A=1<<columns;words=[((),0),None];ix={words[0]:0,None:1};queue=collections.deque(words);rows=[]
 while queue:
  state=queue.popleft();row=[]
  if state is None:rows.append([1]*A);continue
  w,phase=state
  for x in range(A):
   new=None if w and not valid(w[-1],x,columns) else ((w+(x,))[-memory:] if memory else (),(phase+1)%clock)
   if new not in ix:ix[new]=len(words);words.append(new);queue.append(new)
   row.append(ix[new])
  rows.append(row)
 return np.array(rows,dtype=np.int32),words

def column_graph(T,columns):
 first=(-1,0,0);states=[first];ix={first:0};queue=collections.deque([first]);edges=[]
 while queue:
  last,p,q=queue.popleft();u=ix[last,p,q]
  for x in range(1<<columns):
   if last>=0 and not valid(last,x,columns):continue
   y=None if last<0 else emit(last,x,columns);new=(x,int(T[p,x]),q if y is None else int(T[q,y]))
   if new not in ix:ix[new]=len(states);states.append(new);queue.append(new)
   edges.append((u,ix[new],p,x,q,y,(x&1) if last<0 else 0))
 return states,edges

def simple_boundary_graph(T,columns,domain):
 states=[(0,-1)];ix={(0,-1):0};queue=collections.deque(states);edges=[];one=(1<<(columns-1))+1 if columns==3 else 1
 while queue:
  p,r=queue.popleft();u=ix[p,r]
  for s in range(2):
   if domain in ['no00','golden'] and r==0 and s==0:continue
   if domain=='golden' and r==4 and s==1:continue
   rr=(r+1 if r>=0 else 1) if s else 0
   if domain!='golden':rr=s
   q=int(T[p,one]);x=one*s;end=int(T[q,x]);new=(end,rr)
   reward=int(not s and (domain!='all' or r!=0))
   if new not in ix:ix[new]=len(states);states.append(new);queue.append(new)
   edges.append((u,ix[new],p,one,q,x,reward))
 return states,edges

BAD_WORDS=[tuple(map(int,w)) for w in ['00','11111','010110','011010','1011010','01101110','0101011110','0101110110','01101111010','0110111101110']]
def boundary_graph(T,columns,domain):
 if domain!='badclass':return simple_boundary_graph(T,columns,domain)
 states=[(0,())];ix={states[0]:0};queue=collections.deque(states);edges=[];one=5 if columns==3 else 1
 while queue:
  p,hist=queue.popleft();u=ix[p,hist]
  for s in range(2):
   w=hist+(s,)
   if any(w[-len(bad):]==bad for bad in BAD_WORDS):continue
   q=int(T[p,one]);x=one*s;end=int(T[q,x]);new=(end,w[-12:])
   if new not in ix:ix[new]=len(states);states.append(new);queue.append(new)
   edges.append((u,ix[new],p,one,q,x,1-s))
 return states,edges

def synth(columns=2,memory=2,domain='no00',factor=1,seconds=45,charge_all_symbols=False,zero_boundary=False,spatial_multiplier=1,clock=2):
 assert columns in [2,3] and domain in ['all','no00','golden','badclass'] and factor>=0 and spatial_multiplier>=1
 T,words=reader(columns,memory,clock);states,edges=column_graph(T,columns);bs,be=boundary_graph(T,columns,domain)
 labels=[];ix={};rows=[];rhs=[]
 def var(label):
  if label not in ix:ix[label]=len(labels);labels.append(label)
  return ix[label]
 alpha=var(('boundary_charge_rate',));C=lambda p,x:var(('letter_cost',p,x));H=lambda p:var(('terminal_cost',p));Z=lambda u:var(('column_upper',u));L=lambda u:var(('boundary_lower',u))
 def add(terms,b=0):
  row={}
  for j,v in terms:row[j]=row.get(j,Q(0))+v
  rows.append({j:v for j,v in row.items() if v});rhs.append(Q(b))
 for u,v,p,x,q,y,black in edges:
  payment=int(states[u][0]<0) if charge_all_symbols else black
  add([(Z(u),1),(C(p,x),1),(Z(v),-1)]+([] if y is None else [(C(q,y),-spatial_multiplier)]),factor*payment)
 for u,(last,p,q) in enumerate(states):add([(Z(u),1),(H(p),1),(H(q),-spatial_multiplier)])
 for u,v,p,a,q,b,reward in be:add([(L(v),1),(L(u),-1),(C(p,a),-1),(C(q,b),-1)]+([] if zero_boundary else [(alpha,reward)]))
 for u,(p,r) in enumerate(bs):add([(L(u),-1),(H(p),-1)])
 h0=H(0);z0=Z(0);l0=L(0);bounds=[(None,None)]*len(labels)
 for j in [h0,z0,l0]:bounds[j]=(0,0)
 bounds[alpha]=(0,1)
 ii=[];jj=[];vv=[]
 for i,row in enumerate(rows):
  for j,v in row.items():ii.append(i);jj.append(j);vv.append(float(v))
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();target=np.array(list(map(float,rhs)))
 objective=np.zeros(len(labels));objective[alpha]=-1
 started=time.monotonic();fit=linprog(objective,A_ub=A,b_ub=target,bounds=bounds,method='highs-ipm',options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 rec={'columns':columns,'memory':memory,'temporal_clock':clock,'boundary_domain':domain,'spatial_charge_factor':factor,'spatial_multiplier':spatial_multiplier,'calibration_charge_all_symbols':charge_all_symbols,'calibration_zero_boundary':zero_boundary,'reader_states':len(T),'column_graph_states':len(states),'boundary_graph_states':len(bs),'variables':len(labels),'constraints':len(rows),'solver_status':int(fit.status),'solver_message':fit.message,'solver_seconds':round(time.monotonic()-started,3),'all_lengths_encoded_by_graph_potentials':True,'solver_method':'highs-ipm','positive_rate_optimizes_all_finite_charge_coefficients':factor>0,'Lean_verified':False,'CQ01_proved':False}
 if fit.success:
  rec['maximum_residual']=float(np.max(A@fit.x-target));rec['boundary_charge_rate']=float(fit.x[alpha])
  if fit.x[alpha]<=1e-9:return rec
  for den in [100,10000,1000000]:
   values=[Q(float(v)).limit_denominator(den) for v in fit.x]
   if any(values[j]!=0 for j in [h0,z0,l0]) or not(0<values[alpha]<=1):continue
   if all(sum((v*values[j] for j,v in row.items()),Q(0))<=b for row,b in zip(rows,rhs)):
    rec.update({'exact_rational_graph_certificate':True,'rational_boundary_charge_rate':str(values[alpha]),'transition_table':T.tolist(),'reader_words':[None if w is None else [list(w[0]),w[1]] for w in words],'certificate':[{'label':list(l),'value':str(v)} for l,v in zip(labels,values)]});break
 return rec
