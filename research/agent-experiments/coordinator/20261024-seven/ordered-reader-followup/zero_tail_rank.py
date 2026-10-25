"""Synthesize a provisional nonnegative pattern rank for zero even outputs.

Only sampled/exhaustive finite transitions are used here. A fitted rank is
not accepted until its inequality is proved for arbitrary valid widths.
"""
from collections import Counter
import argparse,json,random,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save
from even_code_charge import words
from coupled_even_code_probe import even_code,decode

def step(R,Rm,y):
    acc=y;out=[y]
    for i,a in enumerate(R):
        acc^=a|(0 if i==0 else Rm[i-1]);out.append(acc)
    return out,R

def transitions(free):
    R=[];Rm=[];run=0;initial=0
    for d,s in enumerate(free):
        before=[a+2*(Rm[i] if i<len(Rm) else 0) for i,a in enumerate(R)]
        oldrun=run
        R,Rm=step(R,Rm,1);initial|=R[-1]<<(2*d)
        R,Rm=step(R,Rm,s);e=R[-1];initial|=e<<(2*d+1)
        run=run+1 if s else 0
        after=[a+2*(Rm[i] if i<len(Rm) else 0) for i,a in enumerate(R)]
        yield before,oldrun,after,run,s,e,d

def features(word,run,k):
    padded=[4]*(k-1)+word+[5]*(k-1)
    return Counter((run,tuple(padded[i:i+k])) for i in range(len(padded)-k+1))

def edge_features(edge,k):
    before,r,after,rr,s,e,d=edge
    delta=features(after,rr,k);delta.subtract(features(before,r,k))
    return {p:c for p,c in delta.items() if c},1-s

def random_free(n,rng):
    out=[];run=0
    for i in range(n):
        s=1 if i and run==0 else (0 if run==4 else rng.randrange(2))
        out.append(s);run=run+1 if s else 0
    return out

def controls():
    rng=random.Random(302449);count=0
    for _ in range(16):
        free=random_free(24,rng);packed=0;evens=0
        for _,_,_,_,s,e,d in transitions(free):evens|=e<<d;count+=1
        assert even_code(free)==evens and decode(evens,len(free))==free
    return {'antidiagonal_even_outputs_checked':count,'all_passed':True}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--patterns',type=int,nargs='+',default=[1,2,3,5,7])
    parser.add_argument('--paths',type=int,default=128);parser.add_argument('--refine',action='store_true')
    args=parser.parse_args();filename='zero-tail-rank-refined.json' if args.refine else 'zero-tail-rank.json'
    rng=random.Random(302450);checked=controls();start=time.monotonic()
    train=[[w>>i&1 for i in range(12)] for w in words(12,True)]
    train += [random_free(64,rng) for _ in range(args.paths)]
    held=[random_free(128,rng) for _ in range(64)]
    # Structured low-weight examples were found by a different, frozen search.
    from core import HERE
    for name in ['charge-beam-factor3.json','charge-beam-factor8.json']:
        held += [r['free_prefix'] for r in json.loads((HERE/name).read_text())['records']]
    if args.refine:
        train+=held;held=[random_free(256,rng) for _ in range(32)]
        from empty_right_absorption import step as right_step
        for R in [0,1,2,3,5,17,31,495,255]+[rng.getrandbits(32) for _ in range(7)]:
            x=R;free=[]
            for t in range(512):
                x=right_step(x,t)
                if t%2==0:free.append(1^(x&1))
            held.append(free)
    edges=[];seen=set()
    for free in train:
        prefix=0
        for edge in transitions(free):
            d=edge[-1];prefix|=free[d]<<d
            if edge[-2]==0 and (d,prefix) not in seen:edges.append(edge);seen.add((d,prefix))
    hold_edges=[e for f in held for e in transitions(f) if e[-2]==0]
    out={'records':[],'controls':checked,'training_zero_even_edges':len(edges),
         'heldout_zero_even_edges':len(hold_edges),'Lean_verified':False,
         'uniform_rank_proved':False,'full_problem_solved':False,'refined_with_old_heldout':args.refine}
    for k in args.patterns:
        vocab={};values=[];ii=[];jj=[];rhs=[]
        for i,e in enumerate(edges):
            delta,z=edge_features(e,k);rhs.append(-z)
            for p,c in delta.items():
                if p not in vocab:vocab[p]=len(vocab)
                ii.append(i);jj.append(vocab[p]);values.append(c)
        A=coo_matrix((values,(ii,jj)),shape=(len(edges),len(vocab))).tocsr()
        before=time.monotonic()
        result=linprog(np.ones(len(vocab)),A_ub=A,b_ub=np.array(rhs),bounds=(0,None),
                       method='highs',options={'time_limit':30})
        row={'pattern_length':k,'features':len(vocab),'constraints':len(edges),
             'solver_status':int(result.status),'solver_message':result.message,
             'seconds':round(time.monotonic()-before,3)}
        if result.success:
            weights={p:float(result.x[i]) for p,i in vocab.items() if result.x[i]>1e-10}
            row['nonzero_weights']=len(weights)
            row['training_max_residual']=float(np.max(A@result.x-np.array(rhs)))
            failures=[]
            for edge in hold_edges:
                delta,z=edge_features(edge,k);res=sum(weights.get(p,0)*c for p,c in delta.items())+z
                if res>1e-7:failures.append({'prefix_length':edge[-1]+1,'residual':res,'free_bit':edge[-3]})
            row['heldout_violations']=len(failures);row['first_heldout_failures']=failures[:8]
            if not failures:
                row['provisional_weights']=[{'run':p[0],'pattern':p[1],'weight':v} for p,v in weights.items()]
        out['records'].append(row);save(filename,out)
        print({k:v for k,v in row.items() if k not in ('provisional_weights','first_heldout_failures')},flush=True)
        if result.success and not row['heldout_violations']:break
        if time.monotonic()-start>220:break
    out['seconds']=round(time.monotonic()-start,3);save(filename,out)

if __name__=='__main__':main()
