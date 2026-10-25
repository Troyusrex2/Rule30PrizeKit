"""Falsify multi-step and prefix-parity ranking candidates on zero-even tails.

This is numerical discovery, never a proof premise. A candidate is retained
only for further universal verification, and held-out failures are recorded.
"""
import argparse,random,time,json
from collections import Counter
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import HERE,save
from charge_beam_packed import step,controls
from zero_tail_rank import random_free

def initial(free):
    R=Rm=0
    for d,s in enumerate(free):
        R1,Rold=step(R,Rm,2*d,1)
        R,Rm=step(R1,Rold,2*d+1,s)
    return R,Rm

def word(R,Rm,n):
    return tuple(((R>>j)&1)+2*((Rm>>j)&1) for j in range(2*n))

def tail(free,limit=80,coupled_six=False,coupled_seven=False):
    free=list(free)
    if coupled_six and any(free[j:j+6]==[0,1,0,1,1,0] for j in range(len(free)-5)):return []
    if coupled_seven and any(free[j:j+7]==[1,0,1,1,0,1,0] for j in range(len(free)-6)):return []
    ctxlen=6 if coupled_seven else 5
    R,Rm=initial(free);d=len(free);run=0
    for s in reversed(free):
        if not s:break
        run+=1
    out=[]
    for _ in range(limit):
        R1,Rold=step(R,Rm,2*d,1);base,_=step(R1,Rold,2*d+1,0)
        s=(base>>(2*d+1))&1
        if (s==0 and run==0) or (s==1 and run==4):break
        if coupled_six and free[-5:]+[s]==[0,1,0,1,1,0]:break
        if coupled_seven and free[-6:]+[s]==[1,0,1,1,0,1,0]:break
        ctx=sum(v<<j for j,v in enumerate(free[-ctxlen:])) if coupled_six else run
        before=(word(R,Rm,d),ctx)
        R=base^(((1<<(2*d+2))-1) if s else 0);Rm=R1
        run=run+1 if s else 0;d+=1
        free.append(s)
        assert R>>(2*d-1)==0
        ctx=sum(v<<j for j,v in enumerate(free[-ctxlen:])) if coupled_six else run
        out.append((before,(word(R,Rm,d),ctx),1-s))
    return out

def six_free(n,rng,seven=False):
    f=[]
    def allowed(q):
        return not (q[-2:]==[0,0] or q[-5:]==[1]*5 or q[-6:]==[0,1,0,1,1,0] or
                    (seven and q[-7:]==[1,0,1,1,0,1,0]))
    for _ in range(n):
        choices=[b for b in [0,1] if allowed(f+[b]) and any(allowed(f+[b,c]) for c in [0,1])]
        assert choices
        f.append(rng.choice(choices))
    return f

def features(st,k,parity):
    w,r=st;ans=Counter({(r,'constant'):1})
    if not parity:
        p=(4,)*(k-1)+w+(5,)*(k-1)
        ans.update((r,'window',p[j:j+k]) for j in range(len(p)-k+1))
    else:
        # Prefix parities of the two bit planes and their conjunction.
        a=b=c=0;p=(4,)*(k-1)+w+(5,)*(k-1)
        for j,x in enumerate(w):
            ans[(r,'parity',j%2,a+2*b+4*c,p[j:j+k])]+=1
            a^=x&1;b^=(x>>1)&1;c^=x==3
        ans[(r,'end',a+2*b+4*c,len(w)%2)]+=1
    return ans

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--paths',type=int,default=600)
    parser.add_argument('--blocks',nargs='+',type=int,default=[4,6,8])
    parser.add_argument('--parity',action='store_true');parser.add_argument('--coupled-six',action='store_true')
    parser.add_argument('--coupled-seven',action='store_true');args=parser.parse_args()
    if args.coupled_seven:args.coupled_six=True
    start=time.monotonic();checked=controls();rng=random.Random(302470)
    gen=(lambda n,r:six_free(n,r,args.coupled_seven)) if args.coupled_six else random_free
    train=[tail(gen(rng.randrange(12,81),rng),coupled_six=args.coupled_six,coupled_seven=args.coupled_seven) for _ in range(args.paths)]
    held=[tail(gen(rng.randrange(128,257),rng),coupled_six=args.coupled_six,coupled_seven=args.coupled_seven) for _ in range(args.paths//2)]
    # Long structured examples from an independent low-charge search.
    for name in ['charge-packed-factor5.json','charge-packed-factor8.json']:
        f=json.loads((HERE/name).read_text(encoding='utf-8'))['final_free_prefix']
        held += [tail(f[:n],coupled_six=args.coupled_six,coupled_seven=args.coupled_seven) for n in range(32,min(len(f),513),32)]
    out={'controls':checked,'records':[],'parity_features':args.parity,
         'coupled_six_word_excluded':args.coupled_six,'coupled_seven_word_excluded':args.coupled_seven,
         'context_bits':(6 if args.coupled_seven else 5) if args.coupled_six else 0,
         'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
    for block in args.blocks:
        edges=[(p[j][0],p[j+block-1][1],sum(e[2] for e in p[j:j+block]))
            for p in train for j in range(len(p)-block+1)]
        tests=[(p[j][0],p[j+block-1][1],sum(e[2] for e in p[j:j+block]))
            for p in held for j in range(len(p)-block+1)]
        for k in [1,2,3]:
            vocab={};ii=[];jj=[];data=[];rhs=[]
            for i,(a,b,z) in enumerate(edges):
                delta=features(b,k,args.parity);delta.subtract(features(a,k,args.parity));rhs.append(-z)
                for p,c in delta.items():
                    if not c:continue
                    if p not in vocab:vocab[p]=len(vocab)
                    ii.append(i);jj.append(vocab[p]);data.append(c)
            rec={'block':block,'window':k,'constraints':len(edges),'features':len(vocab),'heldout_edges':len(tests)}
            if not edges:
                rec['status']='no_training_edges';out['records'].append(rec);continue
            A=coo_matrix((data,(ii,jj)),shape=(len(edges),len(vocab))).tocsr()
            fit=linprog(np.ones(len(vocab)),A_ub=A,b_ub=np.array(rhs),bounds=(0,None),
                method='highs',options={'time_limit':18,'primal_feasibility_tolerance':1e-9})
            rec.update({'solver_status':int(fit.status),'solver_message':fit.message})
            if fit.success:
                weights={p:fit.x[i] for p,i in vocab.items() if fit.x[i]>1e-10}
                rec['nonzero_weights']=len(weights);rec['training_max_residual']=float(np.max(A@fit.x-np.array(rhs)))
                bad=[]
                for a,b,z in tests:
                    delta=features(b,k,args.parity);delta.subtract(features(a,k,args.parity))
                    residual=z+sum(weights.get(p,0)*v for p,v in delta.items())
                    if residual>1e-6:bad.append({'input_length':len(a[0])//2,'residual':residual})
                rec['heldout_violations']=len(bad);rec['first_failures']=bad[:5]
                if not bad:rec['candidate_weights']=[{'feature':repr(p),'weight':float(v)} for p,v in weights.items()]
            out['records'].append(rec);out['seconds']=round(time.monotonic()-start,3)
            save('zero-tail-block-rank'+('-seven' if args.coupled_seven else '-six' if args.coupled_six else '')+('-parity' if args.parity else '')+'.json',out)
            print({a:b for a,b in rec.items() if a not in ('candidate_weights','first_failures')},flush=True)
            if time.monotonic()-start>210:return

if __name__=='__main__':main()
