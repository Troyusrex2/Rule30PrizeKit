from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
S=[8,9,16,18,33,36,66,72,132,144]
edges=[[j for j,b in enumerate(S) if (a>>1)==(b&127)] for a in S]
levels=[[{a} for a in range(10)]]
for length in range(1,83):
    levels.append([set().union(*(levels[-1][b] for b in edges[a])) for a in range(10)])
    if all(len(v)==10 for v in levels[-1]):break
else:raise AssertionError('no universal bridge by82')
paths=[]
for a in range(10):
    for b in range(10):
        at=a;path=[S[a]]
        for left in range(length,0,-1):
            at=next(c for c in edges[at] if b in levels[left-1][c]);path.append(S[at])
        assert path[-1]==S[b] and len(path)==length+1
        assert all((x>>1)==(y&127) for x,y in zip(path,path[1:]))
        paths.append(path)
(ROOT/'BRIDGES.json').write_text(json.dumps({'length':length,'words':S,'paths':paths,'all_pairs':100,'kernel_verified':False},separators=(',',':'))+'\n')
print(json.dumps({'bridge_length':length,'paths':len(paths),'edges_checked':length*len(paths)}))
