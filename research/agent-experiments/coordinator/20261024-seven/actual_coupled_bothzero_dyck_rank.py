"""Search ranks on actual driven-right traces, with both newly reconstructed spatial coordinates white.

The learned potential is nonnegative, but universal validity still requires
a proof. Dominance witnesses are retained to diagnose an inadequate feature
family without confusing proxy words with actual coupled trajectories.
"""
import argparse,json,random,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save
from charge_beam_packed import step,controls
from empty_right_absorption import step as right_step
from coupled_even_code_probe import decode,forbidden
from nonlocal_dyck_features import features as stack_features,controls as dyck_controls

def data(initial,N,minimum,cache):
    xr=initial;R=Rm=E=history=0;free=[];edges=[]
    def fea(R,Rm,d):
        key=(R,Rm,d)
        if key not in cache:
            w=tuple((R>>j&1)+2*(Rm>>j&1) for j in range(2*d))
            cache[key]=np.concatenate([stack_features(w),np.array([w.count(i) for i in range(4)],dtype=np.int64)])
        return cache[key]
    for d in range(N):
        xr=right_step(xr,2*d);s=1^(xr&1);xr=right_step(xr,2*d+1)
        R1,old=step(R,Rm,2*d,1);nr,nrm=step(R1,old,2*d+1,s);e=nr>>(2*d+1)&1
        before_ctx=(history>>(d-6))&63 if d>=6 else 0
        history|=s<<d;free.append(s);E|=e<<d
        odd=(R1>>(2*d))&1
        if not e and not odd and d>=max(minimum,6):
            after_ctx=(history>>(d-5))&63
            x=fea(R,Rm,d);y=fea(nr,nrm,d+1)
            edges.append((x,y,before_ctx,after_ctx,1-s,{'initial_right_hex':hex(initial),'depth':d,
                'before_R_hex':hex(R),'before_Rm_hex':hex(Rm),'after_R_hex':hex(nr),'after_Rm_hex':hex(nrm)}))
        R,Rm=nr,nrm
    assert forbidden(free) is None and decode(E&((1<<64)-1),min(64,N))==free[:64]
    return edges

def main():
    p=argparse.ArgumentParser();p.add_argument('--random-paths',type=int,default=48);a=p.parse_args()
    start=time.monotonic();checked={**controls(),**dyck_controls()};rng=random.Random(302521);cache={}
    structured=[0,1,2,3,5,17,31,495]+[1<<k for k in [2,3,7,15,31,63]]+[(1<<k)-1 for k in [2,3,7,15,31,63]]
    initials=structured+[rng.getrandbits(rng.randrange(8,129)) for _ in range(a.random_paths)]
    train=[e for R in initials for e in data(R,128,6,cache)]
    held_initials=[0,1,2,31,495]+[rng.getrandbits(256) for _ in range(8)]
    held=[e for R in held_initials for e in data(R,512,256,cache)]
    phases=sorted({r for e in train+held for r in e[2:4]});ix={r:i for i,r in enumerate(phases)}
    out={'actual_right_dynamics_enforced':True,'zero_odd_and_even_edges_only':True,'training_initial_rows':len(initials),'heldout_initial_rows':len(held_initials),
        'training_depths':[6,127],'heldout_depths':[256,511],'controls':checked,'records':[],
        'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
    for name,selection in [('directed_dyck_and_counts',list(range(len(train[0][0]))))]:
        m=len(selection);ii=[];jj=[];dd=[];rhs=[];dominance=None
        for i,(xx,yy,r,rr,z,meta) in enumerate(train):
            x=xx[selection];y=yy[selection]
            if dominance is None and r==rr and z and np.all(y>=x):dominance={**meta,'phase':r,'before_features':x.tolist(),'after_features':y.tolist()}
            rhs.append(-z)
            if r==rr:y=y-x;x=np.zeros(m,dtype=np.int64)
            for j in np.flatnonzero(x):ii.append(i);jj.append(ix[r]*m+int(j));dd.append(-int(x[j]))
            for j in np.flatnonzero(y):ii.append(i);jj.append(ix[rr]*m+int(j));dd.append(int(y[j]))
        A=coo_matrix((dd,(ii,jj)),shape=(len(train),len(phases)*m)).tocsr();rhs=np.array(rhs)
        fit=linprog(np.ones(len(phases)*m),A_ub=A,b_ub=rhs,bounds=(0,None),method='highs',
            options={'time_limit':30,'primal_feasibility_tolerance':1e-9})
        rec={'features':name,'phases':len(phases),'constraints':len(train),'variables':len(phases)*m,
            'solver_status':int(fit.status),'solver_message':fit.message,'heldout_edges':len(held),
            'actual_dominance_witness':dominance}
        if fit.success:
            W=fit.x.reshape((len(phases),m));bad=[]
            rec['training_max_residual']=float(np.max(A@fit.x-rhs));rec['nonzero_weights']=int((fit.x>1e-10).sum())
            for xx,yy,r,rr,z,meta in held:
                residual=float(W[ix[rr]]@yy[selection]-W[ix[r]]@xx[selection]+z)
                if residual>1e-6:bad.append({**meta,'residual':residual})
            rec['heldout_violations']=len(bad);rec['first_failures']=bad[:4]
            if not bad:rec['provisional_weights']={'phases':phases,'selection':selection,'weights':W.tolist()}
        out['records'].append(rec);out['seconds']=round(time.monotonic()-start,3)
        save('actual-coupled-bothzero-dyck-rank.json',out)
        print({k:v for k,v in rec.items() if k not in ('actual_dominance_witness','first_failures','provisional_weights')},flush=True)

if __name__=='__main__':main()
