"""Try nonnegative quadratic energies with the two checked word guards.

Position-parity counts add signed spatial information. All quadratic forms
are constrained PSD, but numerical fits require exact universal verification.
Longer held-out widths are used to expose finite-length ceiling artifacts.
"""
import argparse,json,random,sys,time
from core import HERE,BASE,save
sys.path.insert(0,str(BASE/'toolchain/semidefinite-research'))
import numpy as np
import scipy.sparse as sp
import cvxpy as cp
from charge_beam_packed import controls
from regular_prefix_bothzero_rank_terminal import trajectory

def feature(st,parity,homogeneous=False):
    w,_=st;x=[w.count(i)/128 for i in range(4)]
    if parity:x.extend((sum(1 if j%2==0 else -1 for j,a in enumerate(w) if a==i))/128 for i in range(4))
    return np.array(x if homogeneous else x+[1.])

def main():
    p=argparse.ArgumentParser();p.add_argument('--paths',type=int,default=700)
    p.add_argument('--homogeneous',action='store_true');a=p.parse_args()
    start=time.monotonic();rng=random.Random(302510);checked=controls()
    initials=[0,1,2,3,5,17,31,495]+[rng.getrandbits(rng.randrange(8,129)) for _ in range(60)]
    rawtrain=[e for R in initials for e in trajectory(R,128,6)]
    rawheld=[e for R in [0,1,2,31,495]+[rng.getrandbits(256) for _ in range(8)] for e in trajectory(R,512,256)]
    train=[((tuple(e[0]),e[2]),(tuple(e[1]),e[3]),e[4]) for e in rawtrain]
    held=[((tuple(e[0]),e[2]),(tuple(e[1]),e[3]),e[4]) for e in rawheld]
    contexts=sorted({st[1] for e in train+held for st in e[:2]});ix={r:i for i,r in enumerate(contexts)}
    out={'actual_right_traces_only':True,'both_spatial_zero_edges':True,'contexts':contexts,'controls':checked,
         'training_depths':[6,127],'heldout_depths':[256,511],'records':[],
         'homogeneous_no_constant_feature':a.homogeneous,
         'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
    for block in [1]:
        edges=train;tests=held
        for parity in [False,True]:
            m=(8 if parity else 4) if a.homogeneous else (9 if parity else 5);ii=[];jj=[];dd=[];rhs=[]
            for i,(before,after,z) in enumerate(edges):
                r,rr=ix[before[1]],ix[after[1]];u=feature(before,parity,a.homogeneous);v=feature(after,parity,a.homogeneous)
                aa=np.outer(u,u).ravel();bb=np.outer(v,v).ravel();rhs.append(-z)
                if r==rr:bb=bb-aa;aa=np.zeros(m*m)
                for j in np.flatnonzero(aa):ii.append(i);jj.append(r*m*m+int(j));dd.append(-float(aa[j]))
                for j in np.flatnonzero(bb):ii.append(i);jj.append(rr*m*m+int(j));dd.append(float(bb[j]))
            A=sp.coo_matrix((dd,(ii,jj)),shape=(len(edges),len(contexts)*m*m)).tocsr();rhs=np.array(rhs)
            Q=[cp.Variable((m,m),symmetric=True) for _ in contexts]
            vec=cp.hstack([cp.reshape(q,(m*m,),order='C') for q in Q])
            prob=cp.Problem(cp.Minimize(sum(cp.trace(q) for q in Q)),[A@vec<=rhs]+[q>>0 for q in Q])
            rec={'block':block,'position_parity_counts':parity,'matrix_dimension':m,
                 'contexts':len(contexts),'constraints':len(edges),'heldout_edges':len(tests)}
            tick=time.monotonic()
            try:
                prob.solve(solver='CLARABEL',max_iter=150,time_limit=35,tol_gap_abs=1e-8,tol_feas=1e-8,tol_gap_rel=1e-8)
                rec['solver_status']=prob.status
            except Exception as error:rec.update({'solver_status':'error_unknown','message':str(error)})
            rec['solver_seconds']=round(time.monotonic()-tick,3)
            if prob.status in ['optimal','optimal_inaccurate'] and all(q.value is not None for q in Q):
                V=[np.array(q.value) for q in Q];flat=np.concatenate([q.ravel() for q in V]);bad=[]
                rec['training_max_residual']=float(np.max(A@flat-rhs));rec['minimum_eigenvalue']=float(min(np.linalg.eigvalsh(q).min() for q in V))
                for before,after,z in tests:
                    u=feature(before,parity,a.homogeneous);v=feature(after,parity,a.homogeneous)
                    residual=float(v@V[ix[after[1]]]@v-u@V[ix[before[1]]]@u+z)
                    if residual>1e-6:bad.append({'width':len(before[0])//2,'residual':residual})
                rec['heldout_violations']=len(bad);rec['first_failures']=bad[:5]
                if not bad and rec['training_max_residual']<1e-6 and rec['minimum_eigenvalue']>=-1e-6:
                    rec['provisional_matrices']=[q.tolist() for q in V]
            out['records'].append(rec);out['seconds']=round(time.monotonic()-start,3)
            save('actual-bothzero-semidefinite-rank'+('-homogeneous' if a.homogeneous else '')+'.json',out)
            print({k:v for k,v in rec.items() if k not in ('provisional_matrices','first_failures')},flush=True)
            if time.monotonic()-start>200:return

if __name__=='__main__':main()
