"""Falsify an unrestricted induction lemma, NOT the Rule30 source claim:
for arbitrary root-swapping positive words of lengths<=3, does its square
have unique fixed-prefix return states at every depth? 100 layers/5000
states/5seconds total. A counterexample need not be reachable from A^P.
"""
from pathlib import Path
from itertools import product
import time,json
R=Path(__file__).resolve().parent;start=time.monotonic()
def sect(word,b):
    out=[]
    for q in reversed(word):out.append(2 if b else (1 if q==2 else 0));b^=q!=0
    return tuple(reversed(out))
tested=0;counter=None;limited=False
for size in [1,2,4]:
    for g in product(range(3),repeat=size):
        if sum(q!=0 for q in g)%2!=1:continue
        if not all(q!=1 or g[(i-1)%len(g)]==2 for i,q in enumerate(g)):continue
        tested+=1;current={g+g:()};seen=set()
        for depth in range(100):
            key=frozenset(current)
            if key in seen:break
            seen.add(key);nxt={}
            if len(current)>5000 or time.monotonic()-start>5:limited=True;break
            for w,path in current.items():
                if sum(q!=0 for q in w)%2:continue
                for b in [0,1]:
                    v=sect(w,b);p=path+(b,)
                    if v in nxt and p!=nxt[v]:
                        counter=dict(g=g,prefix_a=nxt[v],prefix_b=p,section=v,depth=depth+1);break
                    nxt[v]=p
                if counter:break
            if counter:break
            current=nxt
        if counter or limited:break
    if counter or limited:break
out=dict(tested=tested,counterexample=counter,resource_cap=limited,seconds=time.monotonic()-start,
         scope='Only the unrestricted positive-word induction substitute; not a counterexample to SameEdgeRigidity unless the source word is shown reachable from A^P.')
(R/'DOUBLING_LEGAL_PROBE.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
