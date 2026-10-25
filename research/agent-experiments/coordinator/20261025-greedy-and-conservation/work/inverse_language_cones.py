"""Independent exact-size causal cones, avoiding irrelevant future constraints."""
from pathlib import Path
import hashlib,json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root/'solver-deps'))
import z3
target=json.loads((root/'language-filtered-cycles.json').read_text())['best']
prefix=list(map(int,target['prefix_bits']));first=target['alternating_tail_first_bit']
f=prefix+[first^(j%2) for j in range(128-len(prefix))]
started=time.monotonic();records=[]
for n in [8,12,16,20,24,32,48,64,96,128]:
    start=time.monotonic();s=z3.Solver();s.set(timeout=12000,random_seed=303025)
    initial=[z3.BoolVal(True)]+[z3.Bool('r_'+str(p)) for p in range(1,2*n+1)]
    row=initial
    for t in range(2*n-1):
        new=[z3.BoolVal((t+1)%2==0)]
        for p in range(1,len(row)-1):
            b=z3.Bool('c_'+str(t+1)+'_'+str(p));new.append(b)
            s.add(b==z3.Xor(row[p-1],z3.Or(row[p],row[p+1])))
        row=new
        if t%2==0:s.add(row[1]==bool(1-f[t//2]))
    r=s.check();rec={'requested_free_prefix':n,'maximum_initial_position':2*n,'result':str(r),'seconds':time.monotonic()-start}
    if r==z3.unknown:rec['reason']=s.reason_unknown()
    if r==z3.sat:
        model=s.model();code=sum(int(z3.is_true(model.eval(initial[p],model_completion=True)))<<p for p in range(1,len(initial)))
        row=code|1;actual=[];physical={0}|{p for p in range(1,len(initial)) if code>>p&1};other=[]
        for t in range(2*n-1):
            row=((row<<1)^(row|(row>>1)))&~1
            physical={p for p in range(1,max(physical|{1})+2) if int(p-1 in physical)^(int(p in physical)|int(p+1 in physical))}
            if t%2:row|=1;physical.add(0)
            else:actual.append(1-(row>>1&1));other.append(int(1 not in physical))
        assert actual==other==f[:n]
        rec.update({'mathematical_initial_right_hex':hex(code),'independent_physical_replay':True})
    records.append(rec);print(json.dumps(rec),flush=True)
    if r!=z3.sat:break
out={'finite_only':True,'Lean_verified':False,'target':target,'records':records,
     'z3_version':z3.get_version_string(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'seconds':time.monotonic()-started,
     'scope':'All right-half influences included separately for each requested prefix. Solver UNSAT is unverified. Every SAT model checked independently. No infinite realization or finite-R asymptotic claim.'}
(root/'inverse-language-cones.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
