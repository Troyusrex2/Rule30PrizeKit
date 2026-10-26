"""Independent finite-cut controls. No timeout means equal forever."""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent
data=json.loads((root/'explicit-tail.json').read_bytes())
dfa=json.loads((root/'learned-reader.json').read_bytes())['dfa'];start=time.monotonic();reports=[];controls=0
def initial(which,N):
    prefix=data[which+'_prefix'];tail=data['shared_tail']
    return sum(((prefix[k] if k<len(prefix) else tail[(k-len(prefix))%len(tail)])&1)<<k for k in range(N))
def literal(row):
    row=row+[0,0]
    return [(30>>((row[k]<<2)|(row[k+1]<<1)|row[k+2]))&1 for k in range(len(row)-2)]
for T in [0,1,2,3,4,8,16,32,64,128,256,512,1024]:
    N=2*T+8;a=initial('a',N);b=initial('b',N);assert a^b==30
    q=0
    for k in reversed(range(N)):q=dfa['transitions'][q][(((a>>k)&1)<<1)|((b>>k)&1)]
    assert q==15
    horizon=max(4096,8*T+128);first=None
    la=[(a>>k)&1 for k in range(N)];lb=[(b>>k)&1 for k in range(N)]
    for t in range(horizon):
        assert ((a^b)>>4)&1
        if t<=T:assert not ((a^b)&1)
        if (a^b)&1:first=t;break
        if T<=8:
            assert a==sum(v<<k for k,v in enumerate(la)) and b==sum(v<<k for k,v in enumerate(lb))
            controls+=2*N;la=literal(la);lb=literal(lb)
        a^=(a>>1)|(a>>2);b^=(b>>1)|(b>>2)
    assert first is None or first>T
    rec={'requested_delay':T,'finite_prefix_width':N,'reader_state':q,
         'first_observed_difference':first,'search_horizon':horizon,
         'status':'different' if first is not None else 'unknown_after_horizon'}
    reports.append(rec);print(json.dumps(rec),flush=True)
out={'reports':reports,'literal_scalar_controls':controls,'seconds':round(time.monotonic()-start,3),
     'finite_samples_only':True,'Lean_verified':False,'unbounded_eventual_separation_proved':False,'full_problem_solved':False}
(root/'delay-samples.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
