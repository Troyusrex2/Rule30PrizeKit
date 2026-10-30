"""Reuse the width3/4 controlled local model; no absolute-depth census."""
from pathlib import Path
import json,time
R=Path(__file__).resolve().parent;start=time.monotonic();results=[]
for d in [3,4]:
    n=d+2;mask=(1<<n)-1;states=[]
    def step(v,c,h):return (v^(((v<<1)|c)|((v<<2)|(c<<1)|h)))&mask
    for x in range(1<<n):
        for delta in range(1,1<<d,2):
            for c in [0,1]:
                for h in [0,1]:states.append((x,x^delta,c,h))
    idx={s:i for i,s in enumerate(states)};edges=[]
    for x,y,c,h in states:
        a,b=step(x,c,h),step(y,c,h)
        edges.append([idx[(a,b,cp,hp)] for cp in [0,1] for hp in [0,1]
            if (not h or cp!=c) and (a,b,cp,hp) in idx])
    ranks=[0]*len(states);iterations=0
    while True:
        nxt=[max([ranks[v]+s[2] for v in es],default=0) for s,es in zip(states,edges)]
        iterations+=1
        if nxt==ranks:break
        assert iterations<100
        ranks=nxt
    assert all(ranks[v]+s[2]<=ranks[i] for i,(s,es) in enumerate(zip(states,edges)) for v in es)
    out=dict(width=d,states=len(states),max_rank=max(ranks),iterations=iterations,
        rank_histogram={r:ranks.count(r) for r in set(ranks)},ranks=ranks)
    results.append(out)
out=dict(results=results,seconds=time.monotonic()-start,
    target='A rank nonincreasing on every nonleaking step, decreasing when common c is black. Combined with uniform clock bound this could prove arbitrary-depth relative-width escape. Not yet a Lean proof.')
(R/'RELATIVE_RANK.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(results=[{k:v for k,v in x.items() if k!='ranks'} for x in results],seconds=out['seconds'])))
