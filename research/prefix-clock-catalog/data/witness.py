from pathlib import Path
import json,collections,hashlib
ROOT=Path(__file__).resolve().parent;old=ROOT.parent/'periodic-profile-nonloss-20261029'
g=json.loads((old/'attempt01-g913/RESULTS.json').read_text())['graphs'][-1];rank=json.loads((old/'PROFILE-RANK.json').read_text())['ranks'];nodes=g['nodes'];edges=g['edges']
parents={0:None};todo=collections.deque([0])
while todo:
    i=todo.popleft()
    for bit,j in enumerate(edges[i]):
        if j is not None and j not in parents:parents[j]=(i,bit);todo.append(j)
at=rank.index(max(rank));path=[];here=at
while parents[here] is not None:path.append(here);here=parents[here][0]
path.reverse();initial_depth=len(path);start_diagonal=initial_depth-1
while rank[at]>0:
    choices=[j for j in edges[at] if j is not None and rank[j]==rank[at]-1];assert choices
    at=choices[0];path.append(at)
words=[0,0]+[nodes[i][1] for i in path];width=len(path);seed=sum((w&1)<<j for j,w in enumerate(words[2:]));mask=(1<<width)-1
here=seed
for t in range(32):
    for j,w in enumerate(words[2:]):assert ((here>>j)&1)==((w>>t)&1)
    here=(here^((here<<1)|(here<<2)))&mask
assert here==seed
assert ((words[start_diagonal+2]>>2)&1)!=(words[start_diagonal+2]&1)
result={'seed':seed,'width':width,'start_diagonal':start_diagonal,'last_diagonal':width-1,'available_extensions':width-1-start_diagonal,'prefix_period':32,'path':path,'words':words,'scope':'numerical witness; actual-seed Lean bridge still required','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'WITNESS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('path','words')}))
