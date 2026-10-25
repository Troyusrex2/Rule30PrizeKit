"""Try nonnegative position-weighted pattern ranks; numerical candidates only."""
from collections import Counter
import argparse,json,random,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import save,HERE
from zero_tail_rank import transitions,random_free,controls
from even_code_charge import words

def features(word,run,k):
    padded=[4]*(k-1)+word+[5]*(k-1);out=Counter();N=len(padded)-k+1
    for i in range(N):
        p=tuple(padded[i:i+k]);left=i+1;right=N-i
        for mode,v in enumerate([1,left,right,left*left,right*right,left*right]):
            out[(run,p,mode)]+=v
    return out

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--patterns',type=int,nargs='+',default=[1,2,3,5])
    args=parser.parse_args();rng=random.Random(302458);start=time.monotonic();checked=controls()
    train=[[w>>i&1 for i in range(12)] for w in words(12,True)]+[random_free(64,rng) for _ in range(128)]
    held=[random_free(128,rng) for _ in range(64)]
    for name in ['charge-beam-factor3.json','charge-beam-factor8.json']:
        train += [r['free_prefix'] for r in json.loads((HERE/name).read_text())['records']]
    edges=[e for f in train for e in transitions(f) if e[-2]==0]
    out={'controls':checked,'records':[],'position_moments':['1','left','right','left2','right2','left*right'],
         'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
    for k in args.patterns:
        vocab={};ii=[];jj=[];values=[];rhs=[]
        for i,e in enumerate(edges):
            before,r,after,rr,s,_,_=e;rhs.append(-(1-s));delta=features(after,rr,k)
            delta.subtract(features(before,r,k))
            for p,c in delta.items():
                if not c:continue
                if p not in vocab:vocab[p]=len(vocab)
                ii.append(i);jj.append(vocab[p]);values.append(c)
        A=coo_matrix((values,(ii,jj)),shape=(len(edges),len(vocab))).tocsr()
        scales=1/np.maximum(1,np.abs(A).max(axis=1).toarray().ravel())
        result=linprog(np.ones(len(vocab)),A_ub=A.multiply(scales[:,None]).tocsr(),
            b_ub=np.array(rhs)*scales,bounds=(0,None),method='highs-ds',
            options={'time_limit':35,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
        rec={'k':k,'variables':len(vocab),'constraints':len(edges),'solver_status':int(result.status),
             'solver_message':result.message}
        if result.success:
            weights={p:float(result.x[i]) for p,i in vocab.items() if result.x[i]>1e-10}
            rec['nonzero_weights']=len(weights);bad=[];total=0
            rec['unscaled_training_max_residual']=float(np.max(A@result.x-np.array(rhs)))
            for f in held:
                for e in transitions(f):
                    before,r,after,rr,s,even,d=e
                    if even:continue
                    total+=1;delta=features(after,rr,k);delta.subtract(features(before,r,k))
                    residual=sum(weights.get(p,0)*v for p,v in delta.items())+1-s
                    if residual>1e-6:bad.append({'length':d+1,'residual':residual})
            rec['heldout_edges']=total;rec['heldout_violations']=len(bad);rec['first_failures']=bad[:8]
            if not bad:rec['provisional_weights']=[{'run':p[0],'pattern':p[1],'moment':p[2],'weight':v} for p,v in weights.items()]
        out['records'].append(rec);out['seconds']=round(time.monotonic()-start,3)
        save('zero-tail-position-rank.json',out)
        print({a:b for a,b in rec.items() if a not in ('provisional_weights','first_failures')},flush=True)
        if time.monotonic()-start>220:break

if __name__=='__main__':main()
