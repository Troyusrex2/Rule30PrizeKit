from pathlib import Path
import json,time

ROOT=Path(__file__).resolve().parent

def inverse(rows,n):
    a=[r|(1<<(n+i)) for i,r in enumerate(rows)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if (a[i]>>j)&1),None)
        if pivot is None:return None
        a[j],a[pivot]=a[pivot],a[j]
        for i in range(n):
            if i!=j and ((a[i]>>j)&1):a[i]^=a[j]
    return [r>>n for r in a]

def simulate(horizon,K):
    r=1<<K;states=[]
    for _ in range(horizon+1):
        states.append(r);r=(r<<1)^(r|(r>>1))
    return states

def decompose(n,inv,states,K,c):
    obs=[n+i for i in range(n) if (inv[i]>>i)&1]+[2*n]
    linear=len(obs)%2
    green=[1<<K]
    for _ in range(2*n):green.append((green[-1]<<1)^green[-1]^(green[-1]>>1))
    layers=[]
    for s in range(2*n):
        w=0
        for j in obs:
            if s<j:w^=green[j-1-s]
        terms=(states[s]&(states[s]>>1))&w
        layers.append({'source_time':s,'active_terms':terms.bit_count(),'parity':terms.bit_count()%2})
    residual=linear
    for layer in layers:residual^=layer['parity']
    diag_term=sum(((inv[i]>>i)&1)*c[n+i] for i in range(n))%2
    assert residual==c[2*n]^diag_term
    return {'observation_times':obs,'linear_contribution':linear,'source_layers':layers,
            'newest_source':layers[-1]['parity'],'older_contribution':residual^layers[-1]['parity'],
            'pivot':residual}

def main():
    start=time.monotonic();K=132;states=simulate(128,K);c=[(r>>K)&1 for r in states]
    records=[];first=None;checked=0
    for n in range(1,65):
        if time.monotonic()-start>30:raise TimeoutError('preregistered cap')
        h=[sum(c[i+j]<<j for j in range(n)) for i in range(n)];inv=inverse(h,n)
        if inv is None:continue
        checked+=1;u=sum(c[n+i]<<i for i in range(n))
        quadratic=sum(((r&u).bit_count()%2)*((u>>i)&1) for i,r in enumerate(inv))%2
        diag=sum(((inv[i]>>i)&1)*c[n+i] for i in range(n))%2
        assert quadratic==diag
        eps=c[2*n]^diag;fresh=((states[2*n-1]>>K)&1)&((states[2*n-1]>>(K+1))&1)
        hn=[sum(c[i+j]<<j for j in range(n+1)) for i in range(n+1)]
        assert (inverse(hn,n+1) is not None)==bool(eps)
        row={'n':n,'pivot':eps,'newest_source':fresh}
        records.append(row)
        if fresh and not eps and first is None:
            first={**row,'H_rows':h,'inverse_rows':inv,'u':u,'center_prefix':c[:2*n+1],
                   'decomposition':decompose(n,inv,states,K,c)}
    result={'status':'fresh_source_candidate_refuted' if first else 'not_refuted_in_fixed_range',
            'invertible_parents_checked':checked,'records':records,'first_counterexample':first,
            'seconds':time.monotonic()-start,'verification':'Exact finite Python, not Lean'}
    (ROOT/'pivot-result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))

if __name__=='__main__':main()
