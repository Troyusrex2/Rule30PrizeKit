"""Exact controls, witness transfer analysis, and disagreement-path probes."""
from collections import Counter
import importlib.util, itertools, math, time
from core import phi, canonical, save, HERE

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def mul(a,b):
    x,y,z,w=a;v,s,t,u=b
    return (x*v+y*t,x*s+y*u,z*v+w*t,z*s+w*u)

def witness():
    # Full five-cell neighborhoods: output witness has three adjacent outputs.
    nexts={k:set() for k in range(8)}
    for ll,l,c,r,rr in itertools.product(range(2),repeat=5):
        old=4*l+2*c+r
        new=4*(ll^(l|c))+2*(l^(c|r))+(c^(r|rr))
        nexts[old].add(new)
    assert all(len(nexts[k])==(2 if k&1 else 4) for k in range(8))
    m=( (1,1,0,1),(1,1,1,0) )
    periods=[];gold=(1+5**.5)/2
    for p in range(1,13):
        lo=10.;hi=0.; nonempty=0
        for word in itertools.product(range(2),repeat=p):
            a=(1,0,0,1)
            for v in word:a=mul(a,m[v])
            tr=a[0]+a[3];det=a[0]*a[3]-a[1]*a[2]
            rho=(tr+math.sqrt(tr*tr-4*det))/2
            normalized=rho**(1/p)
            lo=min(lo,normalized);hi=max(hi,normalized)
            nonempty+=int(rho>=1)
            # Exact common sub-eigenvector in Z[phi], checked symbolically by
            # the explicit products M0*(phi,1)=(phi+1,1), M1*v=(phi+1,phi).
            assert normalized<=gold+1e-12
        periods.append({'p':p,'words':2**p,'min_radius_per_step':lo,
                        'max_radius_per_step':hi,'nonempty_local_cycle_graphs':nonempty})
    src=next((HERE/'received').glob('r30-coinailyzer-wiki-*/src/witness_entropy.py'))
    mod=load(src,'witness_agent')
    _,wit=mod.evolve(1024)
    a=1
    for t,w in enumerate(wit):
        # physical left at packed index t+1, center t, right t-1.
        right=(a>>(t-1))&1 if t else 0
        assert w==4*((a>>(t+1))&1)+2*((a>>t)&1)+right
        a=phi(a)
    return {'five_cell_cases':32,'successor_sets':{k:sorted(v) for k,v in nexts.items()},
            'uniform_five_cell_conditional_entropy':1.5,
            'independent_phi_witness_controls':len(wit),
            'center_period_matrices':m,'periods':periods,
            'analytic_bound':'common positive v=(golden_ratio,1); M0*v <= golden_ratio*v; M1*v = golden_ratio*v',
            'limitation':'All period words have nonempty local cycle graphs. Radius < 2 is automatic here; it does not imply finite-seed nonperiodicity.'}

def paths(a,b,c,n):
    # Active DAG counts from all initial differing cells in the causal cone.
    # World coordinate p = c - bit_index at time zero.
    counts={p:1 for p in range(-n,n+1) if ((a^b)>>(c-p))&1} if c>=n else {
        c-i:1 for i in range(max(a.bit_length(),b.bit_length())) if (a^b)>>i&1}
    initial=dict(counts);records=[]
    A,B=a,b
    for t in range(n+1):
        actual=((A^B)>>(c+t))&1
        assert counts.get(0,0)%2==actual
        records.append({'t':t,'paths':counts.get(0,0),'difference':actual})
        nxt={}
        for p in range(-n+t+1,n-t):
            def bit(row,q):
                i=c+t-q
                return (row>>i)&1 if i>=0 else 0
            value=counts.get(p-1,0)+(1-bit(A,p+1))*counts.get(p,0)+(1-bit(B,p))*counts.get(p+1,0)
            if value:nxt[p]=value
        counts=nxt;A=phi(A);B=phi(B)
    return {'a':a,'b':b,'c':c,'initial_sources':initial,'records':records}

def disagreement():
    examples=[]
    for a,b,c,n in [(6,5,0,20),(33,45,5,60),(77,56,1,15)]:
        x=paths(a,b,c,n);examples.append(x)
    # Proposed natural certificate: any active source-to-center path =>
    # disagreement. Find earliest false positive on canonical pairs.
    counter=None;tested=0
    for T in range(12):
        for P in range(1,9):
            a,b,c=canonical(T,P);x=paths(a,b,c,24)
            tested+=1
            for item in x['records']:
                if item['paths']>0 and not item['difference']:
                    counter={'T':T,'P':P,'a':a,'b':b,'c':c,**item};break
            if counter:break
        if counter:break
    assert counter
    # Explicit failure of determining right from center and next-center alone.
    triples=[(0,0,0),(1,0,1)]
    assert all(l^(c|r)==0 and c==0 for l,c,r in triples)
    return {'path_parity_controls':examples,'canonical_positive_path_is_not_disagreement':counter,
            'canonical_pairs_until_counter':tested,
            'right_inheritance_local_ambiguity':triples,
            'limitation':'Exact path counting restates the coupled evolution. A non-tautological source pairing remains missing.'}

def main():
    started=time.monotonic()
    out={'witness':witness(),'disagreement':disagreement()}
    out['seconds']=round(time.monotonic()-started,3);save('local-mechanisms.json',out)
    print({'status':'PASS','seconds':out['seconds'],'path_counter':out['disagreement']['canonical_positive_path_is_not_disagreement']})

if __name__=='__main__':main()
