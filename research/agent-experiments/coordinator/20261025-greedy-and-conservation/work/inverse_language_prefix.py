"""Full light-cone inverse design with fresh Boolean cell constraints.
Necessary finite-word constraints are not a proof of finite-right realizability.
"""
from pathlib import Path
import hashlib,json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root/'solver-deps'))
import z3
data=json.loads((root/'language-filtered-cycles.json').read_text())['best']
prefix=list(map(int,data['prefix_bits']));first=data['alternating_tail_first_bit']
N=128;f=prefix+[first^(j%2) for j in range(N-len(prefix))]
started=time.monotonic();solver=z3.Solver();solver.set(timeout=16000,random_seed=303025)
initial=[z3.BoolVal(True)]+[z3.Bool('r_'+str(i)) for i in range(1,2*N+1)]
row=initial;targets=[]
for t in range(2*N-1):
    new=[z3.BoolVal((t+1)%2==0)]
    for p in range(1,len(row)-1):
        b=z3.Bool('c_'+str(t+1)+'_'+str(p));new.append(b)
        solver.add(b==z3.Xor(row[p-1],z3.Or(row[p],row[p+1])))
    row=new
    if t%2==0:targets.append(z3.Not(row[1]))
records=[];last=0
for n in [8,16,24,32,48,64,96,128]:
    for s in range(last,n):solver.add(targets[s]==bool(f[s]))
    last=n;start=time.monotonic();r=solver.check()
    rec={'requested_free_prefix':n,'maximum_initial_position':2*N,'result':str(r),'solve_seconds':time.monotonic()-start}
    if r==z3.unknown:rec['reason']=solver.reason_unknown()
    if r==z3.sat:
        model=solver.model();code=sum(int(z3.is_true(model.eval(initial[p],model_completion=True)))<<p for p in range(1,len(initial)))
        packed=code|1;stream=[]
        physical={0}|{p for p in range(1,len(initial)) if code>>p&1};physical_stream=[]
        for t in range(2*n-1):
            packed=((packed<<1)^(packed|(packed>>1)))&~1
            physical={p for p in range(1,max(physical|{1})+2) if int(p-1 in physical)^(int(p in physical)|int(p+1 in physical))}
            if t%2:packed|=1;physical.add(0)
            else:stream.append(1-(packed>>1&1));physical_stream.append(int(1 not in physical))
        assert stream==physical_stream==f[:n]
        rec['mathematical_initial_right_hex']=hex(code);rec['independent_physical_replay']=True
    records.append(rec);print(json.dumps(rec),flush=True)
    if r!=z3.sat:break
out={'finite_only':True,'Lean_verified':False,'z3_version':z3.get_version_string(),
     'target':data,'target_first128':''.join(map(str,f)),'records':records,'seconds':time.monotonic()-started,
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'Full causal cone includes every right-half influence on requested bits. A reported UNSAT is not kernel-checked. SAT is a finite-prefix witness only; no tail claim.'}
(root/'inverse-language-prefix.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
