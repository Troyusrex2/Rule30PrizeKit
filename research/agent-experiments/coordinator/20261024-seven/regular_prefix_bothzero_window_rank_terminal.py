"""Learn an interpretable finite-state reader and positive prefix-count and terminal-state rank.

Each candidate reads the entire spatial word, retaining noncommutative
prefix information. The potential is a nonnegative sum, so no finite-width
ceiling is assumed. Data are actual coupled traces, not proxy-language words.
"""
import argparse,hashlib,random,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save
from charge_beam_packed import step,controls
from empty_right_absorption import step as right_step
from coupled_even_code_probe import decode,forbidden

def trajectory(initial,N,minimum):
    xr=initial;R=Rm=history=E=0;free=[];rows=[]
    for d in range(N):
        xr=right_step(xr,2*d);s=1^(xr&1);xr=right_step(xr,2*d+1)
        R1,old=step(R,Rm,2*d,1);nr,nrm=step(R1,old,2*d+1,s);e=nr>>(2*d+1)&1
        before=(history>>(d-6))&63 if d>=6 else 0
        history|=s<<d;free.append(s);E|=e<<d
        odd=(R1>>(2*d))&1
        if not e and not odd and d>=minimum:
            X=[(R>>j&1)+2*(Rm>>j&1) for j in range(2*d)]
            Y=[(nr>>j&1)+2*(nrm>>j&1) for j in range(2*d+2)]
            rows.append((X,Y,before,(history>>(d-5))&63,1-s,{'right_initial_hex':hex(initial),'depth':d}))
        R,Rm=nr,nrm
    assert forbidden(free) is None and decode(E&((1<<64)-1),min(64,N))==free[:64]
    return rows

def pad(rows):
    words=[e[0] for e in rows]+[e[1] for e in rows];L=max(map(len,words));a=np.full((len(words),L),4,dtype=np.uint8)
    for j,w in enumerate(words):a[j,:len(w)]=w
    return a,np.array(list(map(len,words)))

def prefix_counts(words,T,lengths):
    B,L=words.shape;k=len(T);state=np.zeros(B,dtype=np.int16);H=np.zeros((B,1+5*k),dtype=np.int32);H[:,0]=1
    ix=np.arange(B)
    for j in range(L):
        tokens=words[:,j];active=tokens<4;rs=ix[active];ss=state[active];tt=tokens[active]
        H[rs,1+4*ss+tt]+=1;state[active]=T[ss,tt]
    H[ix,1+4*k+state]=1
    assert np.array_equal(H.sum(axis=1)-2,lengths)
    for i in range(min(12,B)):
        s=0;h=np.zeros(1+5*k,dtype=np.int32);h[0]=1
        for a in words[i,:lengths[i]]:h[1+4*s+a]+=1;s=int(T[s,a])
        h[1+4*k+s]=1
        assert np.array_equal(h,H[i])
    return H[:B//2],H[B//2:]

def main():
    p=argparse.ArgumentParser();p.add_argument('--models',type=int,default=24);a=p.parse_args();start=time.monotonic();rng=random.Random(302521)
    structured=[0,1,2,3,5,17,31,495]+[1<<k for k in [2,3,7,15,31,63]]+[(1<<k)-1 for k in [2,3,7,15,31,63]]
    initials=structured+[rng.getrandbits(rng.randrange(8,129)) for _ in range(48)]
    train=[e for R in initials for e in trajectory(R,128,6)]
    held=[e for R in [0,1,2,31,495]+[rng.getrandbits(256) for _ in range(8)] for e in trajectory(R,512,256)]
    X,LX=pad(train);HX,HL=pad(held);phases=sorted({r for e in train+held for r in e[2:4]});ix={r:i for i,r in enumerate(phases)}
    graphs=[]
    for width in [1,2,3]:
        k=4**width
        T=np.array([[(4*state+letter)%k for letter in range(4)] for state in range(k)],dtype=np.int16)
        graphs.append(('last_'+str(width)+'_letters',T))
    out={'actual_right_traces_only':True,'zero_odd_and_even_edges_only':True,'terminal_onehot_features':True,'training_edges':len(train),'heldout_edges':len(held),
         'training_depths':[6,127],'heldout_depths':[256,511],'controls':controls(),'records':[],
         'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
    for model,(kind,T) in enumerate(graphs):
        xx,yy=prefix_counts(X,T,LX);m=xx.shape[1];ii=[];jj=[];dd=[];rhs=[]
        for j,e in enumerate(train):
            x,y=xx[j],yy[j];r,rr=ix[e[2]],ix[e[3]];rhs.append(-e[4])
            if r==rr:y=y-x;x=np.zeros(m,dtype=np.int32)
            for h in np.flatnonzero(x):ii.append(j);jj.append(r*m+int(h));dd.append(-int(x[h]))
            for h in np.flatnonzero(y):ii.append(j);jj.append(rr*m+int(h));dd.append(int(y[h]))
        A=coo_matrix((dd,(ii,jj)),shape=(len(train),len(phases)*m)).tocsr();rhs=np.array(rhs)
        fit=linprog(np.ones(len(phases)*m),A_ub=A,b_ub=rhs,bounds=(0,None),method='highs',
            options={'time_limit':20,'primal_feasibility_tolerance':1e-9})
        rec={'model':model,'kind':kind,'reader_states':len(T),'variables':len(phases)*m,
            'solver_status':int(fit.status),'solver_message':fit.message,'transition_table':T.tolist()}
        if fit.success:
            W=fit.x.reshape((len(phases),m));hx,hy=prefix_counts(HX,T,HL);bad=[]
            rec['training_max_residual']=float(np.max(A@fit.x-rhs));rec['nonzero_weights']=int((fit.x>1e-10).sum())
            for j,e in enumerate(held):
                residual=float(W[ix[e[3]]]@hy[j]-W[ix[e[2]]]@hx[j]+e[4])
                if residual>1e-6:bad.append({**e[5],'residual':residual})
            rec['heldout_violations']=len(bad);rec['first_failures']=bad[:4]
            if not bad:rec['provisional_weights']={'phases':phases,'weights':W.tolist()}
        out['records'].append(rec);out['seconds']=round(time.monotonic()-start,3)
        save('regular-prefix-bothzero-window-rank-terminal.json',out);print({k:v for k,v in rec.items() if k not in ('transition_table','first_failures','provisional_weights')},flush=True)
        if time.monotonic()-start>220:break

if __name__=='__main__':main()
