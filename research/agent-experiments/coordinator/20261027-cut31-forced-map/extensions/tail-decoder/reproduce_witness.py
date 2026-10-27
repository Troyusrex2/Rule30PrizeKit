"""Read retained actual gate and independently reconstruct only the four decisive values."""
from pathlib import Path
from functools import lru_cache
import hashlib,json
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for item in json.loads((root/'MANIFEST.json').read_text())['files']:
    assert sha(root/item['path'])==item['sha256']
result=json.loads((root/'factor-control/RESULT.json').read_text())
g=next(h['gate'] for h in result['histories'] if h['history']=='actual_empty')
rule={(0,0,0):0,(0,0,1):1,(0,1,0):1,(0,1,1):1,(1,0,0):1,(1,0,1):0,(1,1,0):0,(1,1,1):0}
visited=set()
@lru_cache(None)
def x(k,t):
    visited.add((k,t))
    if k==0:return 0
    if k==1:return 1 if t%2 else 1-g[t//2]
    middle=x(k-1,t);inner=x(k-2,t);after=x(k-1,t+1)
    candidates=[v for v in (0,1) if rule[v,middle,inner]==after]
    assert len(candidates)==1
    return candidates[0]
def b(j,t):return x(j+31,t)
def ell(j,t):return x(j+30,t)*(1-x(j+31,t))
def m(j,r):return ell(j,2*r)*ell(j,2*r+2)
def y(j,t):
    r=t//2
    if t%2:
        value=b(j,2*r+13)
        for s in [2,3,6,7,10,12]:value^=m(j,r+s)
        return value^(m(j,r+3)*m(j,r+11))
    value=b(j,2*r+12)
    for s in [0,4,6,7,11]:value^=m(j,r+s)
    return value
values=[y(1,0),y(2,0),y(3,0),y(2,1)]
assert values==[0,1,1,1]
assert rule[values[2],values[1],values[0]]==0!=values[3]
saved=json.loads((root/'factor-control/CONES.json').read_text())['actual_empty']
assert all(x(k,t)==saved[k][t] for k,t in list(visited))
assert max(t for k,t in visited if k==1)==58
print(json.dumps({'passed':True,'values_Y1_0_Y2_0_Y3_0_Y2_1':values,'required_rhs':0,'wall_independent':True,'new_forward_trajectory':False}))
