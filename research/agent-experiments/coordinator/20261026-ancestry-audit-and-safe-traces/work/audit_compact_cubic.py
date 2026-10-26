from pathlib import Path
import hashlib,itertools,json
r=Path(__file__).resolve().parent;p=r/'mode-cubic-compact-witness.json';d=json.loads(p.read_bytes())
P=d['clock'];columns=[0]*P;target=0;updates=0
C=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]]
for rownum,(width,encoded) in enumerate(d['rows_width_and_initial_hex']):
    v=int(encoded,16);init=v;wordmask=(1<<width)-1;state=0
    for j in range(width):state=C[state][v>>j&1]
    state=C[state][0];assert state in [0,1,2,3,5]
    g=[];h=[];k=[]
    for t in range(2*P):
        if t==P:assert (v&((1<<(width-2))-1))==(init&((1<<(width-2))-1))
        g.append(v>>(width-1)&1);h.append(v>>(width-2)&1);k.append(v>>(width-3)&1)
        v=(v^((v<<1)|(v<<2)))&wordmask;updates+=1
    assert v==init
    assert all(h[t+P]==1-h[t] and k[t+P]==k[t] for t in range(P))
    q=[g[t+P]^g[t] for t in range(P)]
    rho=[(g[t+P]|h[t+P])^(g[t]|h[t]) for t in range(P)]
    S=[1^rho[t]^rho[(t+1)%P] for t in range(P)]
    target^=q[0]
    for t,b in enumerate(S):columns[t]|=b<<rownum
assert len(d['rows_width_and_initial_hex'])%2==0 and target==1
monomials=1
for degree in range(1,4):
    for term in itertools.combinations(range(P),degree):
        value=(1<<d['row_count'])-1
        for t in term:value&=columns[t]
        assert value.bit_count()%2==0;monomials+=1
assert monomials==43745
out={'passed':True,'witness_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
     'rows':d['row_count'],'clock':P,'packed_scalar_prefix_updates':updates,
     'every_parent_cyclic_and_canonical_checked':True,'older_prefix_P_period_checked':True,
     'all_cubic_moments_checked':monomials,'target_xor':target,'Lean_verified':False,
     'uniform_mode_observer_refuted':False,'full_problem_solved':False}
(r/'compact-cubic-independent-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
