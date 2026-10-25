"""Bounded inverse design, with independent replay of every SAT candidate.
No solver result is a Lean proof, infinite trace, or finite-R asymptotic claim.
"""
from pathlib import Path
import hashlib,json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root/'solver-deps'))
import z3
old=root.parent/'round2-evaluation-20261025T1244'
data=json.loads((old/'wiki-exact-cycle.json').read_text())
prefix=list(map(int,data['prefix_bits']));tailfirst=data['tail_first_bit']
target=prefix+[tailfirst^(j%2) for j in range(160-len(prefix))]
started=time.monotonic();records=[]

def stream(code,n):
    row=code|1;out=[]
    for t in range(2*n-1):
        row=((row<<1)^(row|(row>>1)))&~1
        if t%2:row|=1
        else:out.append(1-((row>>1)&1))
    return out

def scalar(code,n):
    row={0}|{p for p in range(1,code.bit_length()) if (code>>p)&1};out=[]
    for t in range(2*n-1):
        row={p for p in range(1,max(row|{1})+2)
             if int(p-1 in row)^(int(p in row)|int(p+1 in row))}
        if t%2:row.add(0)
        else:out.append(int(1 not in row))
    return out

cases=[('known-W1',12,32,stream(0x888,32)),('forbidden-00',16,2,[0,0])]
cases += [('bad-Golden-prefix',w,n,target[:n]) for w,n in
          [(16,16),(32,32),(64,64),(128,96),(192,96),(64,128),(128,128),(256,128),(128,160),(320,160)]]
for label,w,n,f in cases:
    start=time.monotonic();width=w+2*n+4
    unknown=z3.BitVec('initial_right',w)
    row=(z3.ZeroExt(width-w,unknown)<<1)|z3.BitVecVal(1,width)
    solver=z3.SolverFor('QF_BV');solver.set(timeout=12000,random_seed=303025)
    evenmask=z3.BitVecVal(((1<<width)-1)^1,width)
    for t in range(2*n-1):
        row=((row<<1)^(row|z3.LShR(row,1)))&evenmask
        if t%2:row=row|z3.BitVecVal(1,width)
        else:solver.add(z3.Extract(1,1,row)==z3.BitVecVal(1-f[t//2],1))
    result=solver.check();rec={'label':label,'maximum_initial_position':w,
        'requested_free_bits':n,'result':str(result),'seconds':time.monotonic()-start}
    if result==z3.unknown:rec['reason']=solver.reason_unknown()
    if result==z3.sat:
        code=solver.model().eval(unknown,model_completion=True).as_long()<<1
        assert stream(code,n)==f and scalar(code,n)==f
        longer=stream(code,4000)
        first=next((i for i,(a,b) in enumerate(zip(longer,target)) if a!=b),None)
        rec.update({'mathematical_initial_right_hex':hex(code),'matched_prefix':n,
                    'independent_physical_replay':True,'first_target_mismatch_through160':first,
                    'free_first256':''.join(map(str,longer[:256]))})
    records.append(rec);print(json.dumps(rec),flush=True)
    if label=='known-W1':assert result==z3.sat
    if label=='forbidden-00':assert result==z3.unsat
out={'finite_only':True,'Lean_verified':False,'z3_version':z3.get_version_string(),
     'solver_timeout_ms':12000,'target':data,'target_free_first160':''.join(map(str,target)),
     'records':records,'seconds':time.monotonic()-started,
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'Only finite requested prefixes and finite initial support bounds. UNSAT is a solver report, not a kernel-checked certificate. UNKNOWN proves nothing. SAT models are independently physically replayed.'}
(root/'inverse-driver-design.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'completed':len(records),'seconds':out['seconds']}),flush=True)
