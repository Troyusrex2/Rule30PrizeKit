"""Exact standard-library verifier. Run from the published evidence package."""
from pathlib import Path
from collections import Counter
import json
ROOT=Path(__file__).resolve().parent
def features(x,y):
    return [(8-j,sum(((((x>>(j-q))&1)<<1)|((y>>(j-q))&1))<<(2*(3-q)) for q in range(4))) for j in range(3,9)]
def step(x):return (x^((x<<1)|(x<<2)))&511
for name in ['POTENTIAL_CERTIFICATE.json','POTENTIAL_TWO_STEP_CERTIFICATE.json']:
    c=json.loads((ROOT/'receipts'/name).read_text(encoding='utf-8'));balance=Counter();total=0
    assert (c['K'],c['width'],c['position_index'])==(6,4,'TOP')
    assert c['steps'] in (1,2)
    for p in c['certificate']:
        m,x,y=(p[k] for k in ['weight','x','y'])
        assert isinstance(m,int) and m>0 and 0<x<512 and 0<y<512 and x!=y
        assert x&1 and y&1 and ((x>>1)&1)==((x>>2)&1) and ((y>>1)&1)==((y>>2)&1)
        a,b=x,y;assert a>>7==b>>7
        for _ in range(c['steps']):
            a,b=step(a),step(b);assert a>>7==b>>7
        assert (a,b)==(p['Tx'],p['Ty'])
        for key in features(x,y):balance[key]-=m
        for key in features(a,b):balance[key]+=m
        total+=m
    assert total==c['total_weight'] and all(v==0 for v in balance.values())
    print(json.dumps(dict(certificate=name,exact=True,parentless=True,transitions=len(c['certificate']),total_weight=total)))
