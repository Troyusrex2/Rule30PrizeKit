"""Finite local strategies for signed prefix-peak ranks of complete rows.

Each output prefix may match either the current input prefix or the one
before its last token. A policy chooses by reader state and last token.
All consistent predecessor states are checked, so this is a sufficient
simulation, not a complete decision method for prefix-peak ranks.
"""
import argparse,collections,functools,hashlib,json,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from universal_folded_row_rank import graph
from universal_folded_prefix_peak_lagged import post_states,suffix_paths

@functools.lru_cache(None)
def cached_graph(table):return graph(np.array(table,dtype=np.int16))

def synth(T,policy,seconds=10,toy=False,fixed_zero=False):
 if toy:
  states=[(0,(),0,0),(1,(3,),0,0),(3,(3,1),0,0)];edges=[(0,1,0,3,[]),(1,2,0,1,[(0,3)])];terminals={2:(0,0,[])};live={0,1,2}
 else:states,edges,terminals,live=cached_graph(tuple(tuple(map(int,row)) for row in T))
 post=post_states(T);postindex={p:i for i,p in enumerate(sorted(post))};labels=[];index={};rows=[]
 def var(label):
  if label not in index:index[label]=len(labels);labels.append(label)
  return index[label]
 alpha=var(('reward_rate',));C=lambda p,a:var(('cost',p,a));Z=lambda u:var(('upper',u))
 def add(terms):
  row={}
  for j,v in terms:row[j]=row.get(j,0)+v
  rows.append({j:v for j,v in row.items() if v})
 def selected_terms(u):
  st=states[u];paths=suffix_paths(T,st[2],st[1],1,post);out=[]
  for path in paths:
   p,x=path[0];choose_previous=(policy>>(4*postindex[p]+x))&1
   out.append([(C(p,x),1)] if choose_previous else [])
  return out
 add([(alpha,1),(C(0,3),-1)])
 for u,v,p,x,emitted in edges:add([(Z(u),1),(C(p,x),-1),(Z(v),-1)]+[(C(q,y),1) for q,y in emitted])
 for u in sorted(live):
  if states[u][0]==3:
   for extra in selected_terms(u):add([(Z(u),1),(alpha,1)]+extra)
 for u,(p,r,tail) in terminals.items():
  partial=[]
  if not tail:
   for extra in selected_terms(u):add([(Z(u),1),(alpha,1)]+extra)
  for q,y in tail:
   partial.append((C(q,y),1))
   for extra in selected_terms(u):add([(Z(u),1),(alpha,1)]+partial+extra)
 start=Z(0);bounds=[(None,None)]*len(labels);bounds[alpha]=(0,1);bounds[start]=(0,0)
 if fixed_zero:
  for label,j in index.items():
   if label[0]=='cost':bounds[j]=(0,0)
 if toy and policy==0:
  values=[1 if l[0] in ['reward_rate','cost'] else 0 if l[1]==0 else -1 for l in labels]
  assert all(sum(v*values[j] for j,v in row.items())<=0 for row in rows)
 ii=[];jj=[];vv=[]
 for i,row in enumerate(rows):
  for j,v in row.items():ii.append(i);jj.append(j);vv.append(v)
 A=coo_matrix((vv,(ii,jj)),shape=(len(rows),len(labels))).tocsr();objective=np.zeros(len(labels));objective[alpha]=-1
 fit=linprog(objective,A_ub=A,b_ub=np.zeros(len(rows)),bounds=bounds,method='highs-ipm',options={'time_limit':seconds,'primal_feasibility_tolerance':1e-9})
 rec={'policy':policy,'post_center_states':len(post),'reader_states':len(T),'variables':len(labels),'constraints':len(rows),'live_states':len(live),'local_last_two_prefix_strategy':True,'all_predecessor_states_checked':True,'solver_status':int(fit.status),'solver_message':fit.message}
 if fit.success:
  rec.update({'reward_rate':float(fit.x[alpha]),'maximum_residual':float(np.max(A@fit.x))})
  if fit.x[alpha]>1e-8:
   for denominator in [100,1000,1000000]:
    f=[Fraction(float(v)).limit_denominator(denominator) for v in fit.x]
    if not(0<f[alpha]<=1 and f[start]==0):continue
    if all(sum((v*f[j] for j,v in row.items()),Fraction(0))<=0 for row in rows):
     rec.update({'exact_rational_graph_certificate':True,'rational_reward_rate':str(f[alpha]),'transition_table':T.tolist(),'certificate':[{'label':list(l),'value':str(v)} for l,v in zip(labels,f)]});break
 return rec

def models():
 yield 'constant_post',np.ones((2,4),dtype=np.int16)
 for kind,base in [
  ('left_parity',np.array([[p^(x&1) for x in range(4)] for p in range(2)])),
  ('right_parity',np.array([[p^(x>>1) for x in range(4)] for p in range(2)])),
  ('both_parity',np.array([[p^((x&1)^(x>>1)) for x in range(4)] for p in range(2)])),
  ('clock2',np.array([[1-p]*4 for p in range(2)])),
  ('last_left',np.array([[x&1 for x in range(4)]]*2)),
  ('last_right',np.array([[x>>1 for x in range(4)]]*2))]:
  T=np.ones((3,4),dtype=np.int16);T[1:]=1+base;yield kind,T

def write_atomic(path,report):
 raw=(json.dumps(report,indent=2)+'\n').encode();temp=path.with_suffix('.tmp');temp.write_bytes(raw)
 for attempt in range(100):
  try:temp.replace(path);return
  except PermissionError:
   if attempt==99:raise
   time.sleep(.05)

def main():
 p=argparse.ArgumentParser();p.add_argument('--models',nargs='+',type=int,required=True);p.add_argument('--seconds',type=float,default=210);a=p.parse_args();root=Path(__file__).resolve().parent;out=root/'results';out.mkdir(exist_ok=True)
 source={n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in ['folded_peak_policy.py','universal_folded_row_rank.py','universal_folded_prefix_peak_lagged.py']};name='peak-policies-'+'-'.join(map(str,a.models));target=out/(name+'.json');start=time.monotonic();allmodels=list(models());tasks=[]
 for m in a.models:
  kind,T=allmodels[m];count=1<<(4*len(post_states(T)))
  for policy in range(count):tasks.append((m,kind,T,policy))
 report={'source_sha256':source,'model_indices':a.models,'tasks_planned':len(tasks),'next_task':0,'records':[],'arbitrary_radius_product_graphs':True,'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 if target.exists():
  report=json.loads(target.read_text());assert report['source_sha256']==source and report['model_indices']==a.models
 for taskindex in range(report['next_task'],len(tasks)):
  m,kind,T,policy=tasks[taskindex];r=synth(T,policy);r.update({'model':m,'kind':kind});report['records'].append(r);report['next_task']=taskindex+1;report['complete']=taskindex+1==len(tasks);report['seconds_this_run']=round(time.monotonic()-start,3)
  if (taskindex+1)%16==0 or r.get('exact_rational_graph_certificate') or time.monotonic()-start>a.seconds:
   write_atomic(target,report);print({'shard':name,'next_task':taskindex+1,'planned':len(tasks),'status':dict(collections.Counter(x['solver_status'] for x in report['records'])),'candidates':sum(x.get('exact_rational_graph_certificate',False) for x in report['records']),'seconds':report['seconds_this_run']},flush=True)
  if r.get('exact_rational_graph_certificate') or time.monotonic()-start>a.seconds:break
 write_atomic(target,report)
if __name__=='__main__':main()
