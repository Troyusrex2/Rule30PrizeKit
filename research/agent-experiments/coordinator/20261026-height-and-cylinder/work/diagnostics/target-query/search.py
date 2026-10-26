"""One bounded genuine-white cyclic embedding query, not a width census."""
from pathlib import Path
import hashlib,json,sys,time
sys.path.insert(0,r'D:\MWB\Rule30\toolchain\python-research')
import z3
root=Path(__file__).resolve().parent
N=64;P=32;small=182
target=sum(((small>>(t%8))&1)<<t for t in range(P))
assert all(((target>>t)&1) or ((target>>((t+1)%P))&1) for t in range(P))
assert any(not ((target>>t)&1) for t in range(0,P,2))
assert any(not ((target>>t)&1) for t in range(1,P,2))
def literal_step(row,width):return (row ^ ((row<<1)|(row<<2))) & ((1<<width)-1)
def ror(v,k):return ((v>>k)|(v<<(P-k)))&((1<<P)-1)
controls=[]
for text in ['100001','10000001','1111011']:
    w=sum(int(b)<<j for j,b in enumerate(text));rows=[w]
    for t in range(P):rows.append(literal_step(rows[-1],len(text)))
    assert rows[P]==rows[0]
    profiles=[sum(((rows[t]>>j)&1)<<t for t in range(P)) for j in range(len(text))]
    for j,x in enumerate(profiles):
        p=profiles[j-1] if j else 0;r=profiles[j-2] if j>=2 else 0
        assert ror(x,1)==x^(p|r)
    controls.append({'word':text,'rows':rows,'profiles':profiles,'cycle_wrap_checked':True})
(root/'orientation-controls.json').write_bytes((json.dumps({'passed':True,'controls':controls},indent=2)+'\n').encode())
s=z3.Solver();s.set(timeout=240000,random_seed=0)
x=[z3.BitVec('column_'+str(j),P) for j in range(N)]
zero=z3.BitVecVal(0,P)
for j in range(N):
    a=x[j-1] if j else zero;b=x[j-2] if j>=2 else zero
    s.add(z3.RotateRight(x[j],1)==x[j]^(a|b))
s.add(x[-1]==z3.BitVecVal(target,P))
s.add(z3.Or([z3.Extract(0,0,col)!=z3.Extract(8,8,col) for col in x]))
raw=(s.sexpr()+'\n(check-sat)\n').encode();(root/'query.smt2').write_bytes(raw)
start=time.monotonic();result=s.check();elapsed=time.monotonic()-start
out={'result':str(result),'solver':z3.get_version_string(),'seconds':elapsed,'timeout_ms':240000,'width_bound':N,'whole_period_divides':P,'target_time_word':'01101101','target_small_mask':small,'target_full_mask':target,'genuine_white_boundary':True,'actual_shared_recurrence_every_column':True,'explicit_F8_failure':True,'orientation_controls_passed':True,'smt2_sha256':hashlib.sha256(raw).hexdigest(),'kernel_verified':False,'scope':'A single bounded embedding query. UNSAT/unknown does not establish D3 or safety completeness.'}
if result==z3.sat:
    m=s.model();profiles=[m.eval(col).as_long() for col in x]
    rows=[sum(((profiles[j]>>t)&1)<<j for j in range(N)) for t in range(P)]
    for t in range(P):assert literal_step(rows[t],N)==rows[(t+1)%P]
    assert rows[8]!=rows[0]
    assert profiles[-1]==target
    assert all(((row>>(N-1))&1) or ((rows[(t+1)%P]>>(N-1))&1) for t,row in enumerate(rows))
    out.update(initial_word=''.join(str((rows[0]>>j)&1) for j in range(N)),rows=rows,profiles=profiles,literal_full_orbit_audit_passed=True)
elif result==z3.unknown:out['reason_unknown']=s.reason_unknown()
out['solver_statistics']=str(s.statistics())
(root/'result.json').write_bytes((json.dumps(out,indent=2)+'\n').encode())
print(json.dumps({k:out[k] for k in ['result','seconds','width_bound','whole_period_divides','target_time_word','kernel_verified']}))
