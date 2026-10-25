"""Search a spatial flux inequality, not a time-descending nonnegative rank.

A signed finite-column potential can telescope across the finite triangular
inverse computation. Finite fits require a separate universal certificate.
"""
import itertools,time
from collections import Counter
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save

def features(w,k):
 p=(4,)*(k-1)+w+(5,)*(k-1)
 return Counter(p[i:i+k] for i in range(len(p)-k+1))

def after(w):
 return tuple(((w[j+1]&1)^((w[j]&1)|(w[j]>>1)))+2*(w[j]&1) for j in range(len(w)-1))

def valid(w):return all(not (w[j]>>1) or ((w[j]&1)!=(w[j+1]>>1)) for j in range(len(w)-1))

def boundary(f):return tuple(v for s in f for v in (1,s))
def zero_runs(f):return sum(not s and (not i or f[i-1]) for i,s in enumerate(f))

def main():
 start=time.monotonic();out={'adjacent_columns_SFT_enforced':True,'family':'signed column-window flux with finite spatial telescope','records':[],'Lean_verified':False,'uniform_bound_proved':False,'full_problem_solved':False}
 for k in [1,2,3,4]:
  vocab={};rows=[];rhs=[];ii=[];jj=[];vv=[]
  def add(delta,b):
   row=len(rhs);rhs.append(b)
   for p,v in delta.items():
    if v:
     if p not in vocab:vocab[p]=len(vocab)
     ii.append(row);jj.append(vocab[p]);vv.append(v)
  empty=features((),k);add(empty,0);add({p:-v for p,v in empty.items()},0)
  for L in range(1,9):
   for w in itertools.product(range(4),repeat=L):
    if not valid(w):continue
    delta=features(w,k);delta.subtract(features(after(w),k));add(delta,w[0]&1)
  for n in range(1,9):
   for f in itertools.product(range(2),repeat=n):add({p:-v for p,v in features(boundary(f),k).items()},-zero_runs(f))
  A=coo_matrix((vv,(ii,jj)),shape=(len(rhs),len(vocab))).tocsr();b=np.array(rhs)
  fit=linprog(np.zeros(len(vocab)),A_ub=A,b_ub=b,bounds=(None,None),method='highs',options={'time_limit':40,'primal_feasibility_tolerance':1e-9})
  rec={'window':k,'variables':len(vocab),'constraints':len(rhs),'solver_status':int(fit.status),'solver_message':fit.message}
  if fit.success:
   weights={p:fit.x[i] for p,i in vocab.items()};val=lambda w:sum(weights.get(p,0)*v for p,v in features(w,k).items());bad=[]
   rec['training_max_residual']=float(np.max(A@fit.x-b))
   for w in itertools.product(range(4),repeat=9):
    if not valid(w):continue
    residual=val(w)-val(after(w))-(w[0]&1)
    if residual>1e-7:bad.append({'word':list(w),'residual':residual})
   rec['heldout_length9_violations']=len(bad);rec['first_failures']=bad[:3]
   if not bad:rec['provisional_weights']=[{'pattern':list(p),'weight':float(v)} for p,v in weights.items() if abs(v)>1e-9]
  out['records'].append(rec);out['seconds']=round(time.monotonic()-start,3);save('spatial-flux-rank-valid.json',out)
  print({p:v for p,v in rec.items() if p not in ['first_failures','provisional_weights']},flush=True)
if __name__=='__main__':main()
