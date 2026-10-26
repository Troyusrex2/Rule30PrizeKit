"""One genuine finite-white height2 counterexample query; stop after this clock."""
from pathlib import Path
import hashlib,json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,'D:/MWB/Rule30/toolchain/python-research')
import z3
P=32;W=20;solver=z3.Solver();solver.set(timeout=90000)
x=[z3.BitVec('x'+str(j),P) for j in range(W)]
zero=z3.BitVecVal(0,P)
for j in range(W):solver.add(z3.RotateRight(x[j],1)==(x[j]^((x[j-1] if j else zero)|(x[j-2] if j>=2 else zero))))
solver.add(z3.RotateRight(x[-1],8)!=x[-1])
h=[z3.Int('h'+str(t)) for t in range(P+1)];lo=z3.Int('lo')
solver.add(h[0]==0,h[-1]==0,lo>=-2,lo<=0)
for t in range(P):solver.add(h[t+1]==h[t]+z3.If(z3.Extract(t,t,x[-1])==0,(-1 if t%2 else 1),0))
for v in h:solver.add(v>=lo,v<=lo+2)
query=solver.to_smt2();(root/'height2-query.smt2').write_text(query,encoding='utf-8')
start=time.monotonic();status=solver.check();elapsed=time.monotonic()-start
result={'period_return':P,'width':W,'status':str(status),'solver_seconds':elapsed,'solver_timeout_ms':90000,'query_sha256':hashlib.sha256(query.encode()).hexdigest(),'scope':'One exact cyclic32-clock true-white width20 query. No all-width/all-clock conclusion.','kernel_verified':False}
if status==z3.sat:
    m=solver.model();profiles=[m.eval(v).as_long() for v in x]
    rows=[[int(profiles[j]>>t&1) for j in range(W)] for t in range(P)]
    for t in range(P):
        old=rows[t];new=[v ^ ((old[j-1] if j else 0)|(old[j-2] if j>=2 else 0)) for j,v in enumerate(old)]
        assert new==rows[(t+1)%P]
    trace=[r[-1] for r in rows];least=min(q for q in range(1,P+1) if all(trace[t]==trace[(t+q)%P] for t in range(P)))
    assert least in (16,32)
    heights=[0]
    for t,b in enumerate(trace):heights.append(heights[-1]+(-1 if t%2 else 1)*(1-b))
    assert heights[-1]==0 and max(heights)-min(heights)<=2
    result['witness']={'word':''.join(map(str,rows[0])),'rows':[''.join(map(str,r)) for r in rows],'least_trace_period':least,'white_height':heights,'white_height_span':max(heights)-min(heights),'white_height_drift':heights[-1],'literal_replay_pass':True}
elif status==z3.unknown:result['reason_unknown']=solver.reason_unknown()
(root/'height2-result.json').write_bytes((json.dumps(result,indent=2)+'\n').encode())
print(json.dumps({k:v for k,v in result.items() if k!='witness'}))
if 'witness' in result:print(json.dumps({k:v for k,v in result['witness'].items() if k not in ('rows','white_height')}))
