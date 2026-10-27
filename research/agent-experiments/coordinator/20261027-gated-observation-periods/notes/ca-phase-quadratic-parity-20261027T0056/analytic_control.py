from pathlib import Path
import json
root=Path(__file__).resolve().parent
n=seed=int('100000',2); orbit=[]
for k in range(256):
    scalar=sum((((n>>i)&1)^(((n>>(i+1))&1)|((n>>(i+2))&1)))<<i for i in range(n.bit_length()))
    nxt=n^((n>>1)|(n>>2))
    assert scalar==nxt
    orbit.append(n); n=nxt
    if n==seed: break
else: raise AssertionError('Missing tiny return')
assert len(orbit)%2==0
p=len(orbit)//2
r=[orbit[2*t]&1 for t in range(p)]
s=[orbit[2*t+1]&1 for t in range(p)]
assert all(v==0 for v in r)
result={'tail':'000','least_T_period':p,'D_orbit':orbit,'r':r,'s':s,
        'Qeven':sum(r[t]*s[t] for t in range(p))%2,
        'Qodd':sum(s[t]*r[(t+1)%p] for t in range(p))%2,
        'scalar_crosscheck':True,'both_orientations_refuted':True}
assert result['Qeven']==result['Qodd']==0
(root/'ANALYTIC-CONTROL.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
