"""Audit saved quadratic obstructions independently of the matrix producer."""
from pathlib import Path
import hashlib,itertools,json,time

r=Path(__file__).resolve().parent;start=time.monotonic();reports=[]
for P in [32,64]:
    path=r/f'mode-quadratic-negative-P{P}.json'
    data=json.loads(path.read_bytes());rows=data['rows'];mask=(1<<P)-1
    assert len(rows)==data['size'] and len(rows)%2==0
    columns=[0]*P;target=0;cells=0
    for rownum,row in enumerate(rows):
        field=row['initial_parent'].copy();initial=field.copy()
        observation=[];newer=[];older=[]
        for t in range(2*P):
            newer.append(field[-1]);older.append(field[-2]);observation.append(field[-1]|field[-2])
            field=[(30>>(4*x+2*(field[i-1] if i>0 else 0)+(field[i-2] if i>1 else 0)))&1
                   for i,x in enumerate(field)]
            cells+=len(field)
        assert field==initial
        assert all(older[t+P]==1-older[t] for t in range(P))
        q=[newer[t+P]^newer[t] for t in range(P)]
        rho=[observation[t+P]^observation[t] for t in range(P)]
        S=[1^(rho[(t+1)%P]^rho[t]) for t in range(P)]
        assert sum(b<<t for t,b in enumerate(q))==row['mode']
        assert sum(b<<t for t,b in enumerate(S))==row['derived_observation']
        assert sum(b<<t for t,b in enumerate(rho))==row['rho']
        target^=q[0]
        for t in range(P):columns[t]|=S[t]<<rownum
    assert target==1
    assert all(c.bit_count()%2==0 for c in columns)
    assert all((columns[i]&columns[j]).bit_count()%2==0 for i,j in itertools.combinations(range(P),2))
    reports.append({'clock':P,'rows':len(rows),'literal_cell_updates':cells,
                    'all_degree_le_two_moments_zero':True,'target_xor':target,
                    'witness_sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
out={'passed':True,'reports':reports,'Lean_verified':False,
     'refutes_only_quadratic_mode_decoder_at_fixed_clock':True,
     'uniform_observer_refuted':False,'full_problem_solved':False,
     'seconds':round(time.monotonic()-start,3)}
(r/'mode-witness-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
