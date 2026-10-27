from pathlib import Path
import json
root=Path(__file__).resolve().parent
def d(n): return n^((n>>1)|(n>>2))
def scalar(n):
    return sum((((n>>i)&1)^(((n>>(i+1))&1)|((n>>(i+2))&1)))<<i for i in range(n.bit_length()))
rows=[]
for tail in ['0','1','00','01','10','11']:
    seed=int('100'+tail,2); n=seed; orbit=[]
    for k in range(256):
        assert d(n)==scalar(n)
        orbit.append(n)
        n=d(n)
        if n==seed: break
    else: raise AssertionError('Unexpected missing tiny return')
    assert len(orbit)%2==0
    p=len(orbit)//2
    r=[orbit[2*t]&1 for t in range(p)]
    s=[orbit[2*t+1]&1 for t in range(p)]
    qe=sum(a*b for a,b in zip(r,s))%2
    qo=sum(s[t]*r[(t+1)%p] for t in range(p))%2
    rows.append({'tail':tail,'D_orbit':orbit,'least_T_period':p,'r':r,'s':s,
                 'Qeven':qe,'Qodd':qo,'candidate_holds':(qe,qo)==(0,1)})
    if (qe,qo)!=(0,1): break
result={'controls':rows,'candidate_refuted':any(not x['candidate_holds'] for x in rows),
        'no_oversized_period':True,'scalar_crosscheck':True}
(root/'CONTROL.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
