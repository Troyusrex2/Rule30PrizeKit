"""Extract an exact Farkas obstruction from actual both-zero trajectories.

The LP proposes multipliers. Integer arithmetic independently verifies the
certificate; infeasibility is not inferred solely from a floating status.
"""
import json,math,random,time
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save
from regular_prefix_bothzero_rank_terminal import trajectory

def main():
 start=time.monotonic();rng=random.Random(302521)
 structured=[0,1,2,3,5,17,31,495]+[1<<k for k in [2,3,7,15,31,63]]+[(1<<k)-1 for k in [2,3,7,15,31,63]]
 initials=structured+[rng.getrandbits(rng.randrange(8,129)) for _ in range(48)]
 edges=[e for R in initials for e in trajectory(R,128,6)];phases=sorted({r for e in edges for r in e[2:4]});ix={r:i for i,r in enumerate(phases)}
 rows=[];cost=[];ii=[];jj=[];vv=[]
 for i,e in enumerate(edges):
  x=[1]+[e[0].count(a) for a in range(4)];y=[1]+[e[1].count(a) for a in range(4)]
  row={}
  for j in range(5):row[ix[e[2]]*5+j]=row.get(ix[e[2]]*5+j,0)-x[j]
  for j in range(5):row[ix[e[3]]*5+j]=row.get(ix[e[3]]*5+j,0)+y[j]
  rows.append(row);cost.append(e[4])
  for j,v in row.items():
   if v:ii.append(i);jj.append(j);vv.append(v)
 A=coo_matrix((vv,(ii,jj)),shape=(len(edges),5*len(phases))).tocsr()
 fit=linprog(np.ones(len(edges)),A_ub=-A.T,b_ub=np.zeros(A.shape[1]),A_eq=np.array([cost]),b_eq=[1.0],bounds=(0,None),method='highs')
 assert fit.success,fit.message
 support=[i for i,y in enumerate(fit.x) if y>1e-8];certificate=None
 for limit in [100,1000,10000,1000000,1000000000]:
  ys=[Fraction(float(fit.x[i])).limit_denominator(limit) for i in support];den=math.lcm(*[v.denominator for v in ys]);weights=[int(y*den) for y in ys];g=math.gcd(*weights);weights=[v//g for v in weights]
  col=[sum(w*rows[i].get(j,0) for i,w in zip(support,weights)) for j in range(A.shape[1])];reward=sum(w*cost[i] for i,w in zip(support,weights))
  if min(col)>=0 and reward>0:
   certificate={'integer_multipliers':weights,'edge_indices':support,'aggregate_feature_delta':col,'positive_aggregate_free_zeros':reward,'minimum_aggregate_column':min(col),'exact_integer_arithmetic_passed':True,
    'edges':[{'initial_right_hex':edges[i][5]['right_initial_hex'],'depth':edges[i][5]['depth'],'phase_before':edges[i][2],'phase_after':edges[i][3],
      'before_features':[1]+[edges[i][0].count(a) for a in range(4)],'after_features':[1]+[edges[i][1].count(a) for a in range(4)],'zero_reward':cost[i]} for i in support]};break
 assert certificate
 out={'family':'nonnegative phase-conditioned affine letter-count potential','phase_order':phases,'variables':A.shape[1],'training_edges':len(edges),'support_size':len(support),'certificate':certificate,
      'meaning':'No nonnegative weights in this feature family can decrease by free-zero reward on every listed actual transition with both new spatial coordinates zero.',
      'not_a_general_ranking_impossibility':True,'Lean_verified':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
 save('bothzero-linear-obstruction.json',out);print({'support_size':len(support),'exact_integer_certificate':True,'positive_reward':reward,'max_multiplier':max(weights),'seconds':out['seconds']},flush=True)
if __name__=='__main__':main()
