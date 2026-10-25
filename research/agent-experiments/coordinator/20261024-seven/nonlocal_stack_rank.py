"""Search positive ranks built from nonlocal stack reductions, not letter counts.

Free-group and involutive-word reductions allow cancellations over arbitrary
distances. Any fitted weights require exact universal verification; finite
fit success alone is not a theorem.
"""
import argparse,random,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save
from charge_beam_packed import controls
from zero_tail_block_rank import tail,six_free

INVERSIONS=[(1,0,3,2),(2,3,0,1),(3,2,1,0)]

def reduce_word(w,inv):
    stack=[];peak=0
    for a in w:
        if stack and stack[-1]==inv[a]:stack.pop()
        else:stack.append(a);peak=max(peak,len(stack))
    lo=0;hi=len(stack)
    while hi-lo>1 and stack[lo]==inv[stack[hi-1]]:lo+=1;hi-=1
    return len(stack),hi-lo,peak

def features(w):
    ans=[1]
    modes=[(w,inv) for inv in INVERSIONS]+[(w,(0,1,2,3))]
    modes += [([a for a in w if a!=skip],(0,1,2,3)) for skip in range(4)]
    modes += [([(mask>>a)&1 for a in w],(0,1)) for mask in range(1,8)]
    for word,inv in modes:
        n,cyclic,peak=reduce_word(word,inv);rpeak=reduce_word(reversed(word),inv)[2]
        ans += [n,cyclic,peak,rpeak]
    return np.array(ans,dtype=np.int64)

def cancellation_controls():
    rng=random.Random(302514);count=0
    for inv in INVERSIONS+[(0,1,2,3)]:
        for n in range(13):
            for _ in range(4):
                w=[rng.randrange(4) for _ in range(n)];at=rng.randrange(n+1);a=rng.randrange(4)
                inserted=w[:at]+[a,inv[a]]+w[at:]
                assert reduce_word(w,inv)[:2]==reduce_word(inserted,inv)[:2];count+=1
    return {'inverse_pair_insertion_controls':count,'all_passed':True}

def main():
    p=argparse.ArgumentParser();p.add_argument('--paths',type=int,default=700);a=p.parse_args();start=time.monotonic()
    checked={**controls(),**cancellation_controls()};rng=random.Random(302515)
    train=[tail(six_free(rng.randrange(16,257),rng,True),coupled_six=True,coupled_seven=True) for _ in range(a.paths)]
    heldrng=random.Random(302516)
    held=[tail(six_free(heldrng.randrange(512,1025),heldrng,True),coupled_six=True,coupled_seven=True) for _ in range(a.paths//3)]
    out={'controls':checked,'training_widths':[16,256],'heldout_widths':[512,1024],
         'feature_family':'nonnegative stack length, cyclic norm, prefix and suffix maxima',
         'feature_count':61,'records':[],'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
    for block in [1,4]:
        edges=[(q[j][0],q[j+block-1][1],sum(e[2] for e in q[j:j+block])) for q in train for j in range(len(q)-block+1)]
        tests=[(q[j][0],q[j+block-1][1],sum(e[2] for e in q[j:j+block])) for q in held for j in range(len(q)-block+1)]
        phases=sorted({st[1] for e in edges+tests for st in e[:2]});ix={r:i for i,r in enumerate(phases)}
        m=61;ii=[];jj=[];data=[];rhs=[]
        for i,(before,after,z) in enumerate(edges):
            x=features(before[0]);y=features(after[0]);r,rr=ix[before[1]],ix[after[1]];rhs.append(-z)
            if r==rr:y=y-x;x=np.zeros(m,dtype=np.int64)
            for j in np.flatnonzero(x):ii.append(i);jj.append(r*m+int(j));data.append(-int(x[j]))
            for j in np.flatnonzero(y):ii.append(i);jj.append(rr*m+int(j));data.append(int(y[j]))
        A=coo_matrix((data,(ii,jj)),shape=(len(edges),len(phases)*m)).tocsr();rhs=np.array(rhs)
        fit=linprog(np.ones(len(phases)*m),A_ub=A,b_ub=rhs,bounds=(0,None),method='highs',
            options={'time_limit':30,'primal_feasibility_tolerance':1e-9})
        rec={'block':block,'phases':len(phases),'constraints':len(edges),'variables':len(phases)*m,
             'solver_status':int(fit.status),'solver_message':fit.message,'heldout_edges':len(tests)}
        if fit.success:
            weights=fit.x.reshape((len(phases),m));bad=[]
            rec['training_max_residual']=float(np.max(A@fit.x-rhs));rec['nonzero_weights']=int((fit.x>1e-10).sum())
            for before,after,z in tests:
                residual=float(weights[ix[after[1]]]@features(after[0])-weights[ix[before[1]]]@features(before[0])+z)
                if residual>1e-6:bad.append({'width':len(before[0])//2,'residual':residual})
            rec['heldout_violations']=len(bad);rec['first_failures']=bad[:6]
            if not bad:rec['provisional_weights']={'phases':phases,'weights':weights.tolist()}
        out['records'].append(rec);out['seconds']=round(time.monotonic()-start,3)
        save('nonlocal-stack-rank.json',out);print({k:v for k,v in rec.items() if k not in ('first_failures','provisional_weights')},flush=True)
        if time.monotonic()-start>220:break

if __name__=='__main__':main()
