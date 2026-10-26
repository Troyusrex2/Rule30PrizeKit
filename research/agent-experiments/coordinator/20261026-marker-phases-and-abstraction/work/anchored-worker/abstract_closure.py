"""Finite Boolean abstraction test, not a width or clock sweep.
The genuine seed is extracted from the already-known fixed word11011001001.
The fixed falsification target is the sealed mixed strip; no new strip search.
"""
from pathlib import Path
import json,hashlib,collections
root=Path(__file__).resolve().parent
fixed=root/'input-mixed-strip.json'
target=json.loads(fixed.read_bytes())['profiles']
word=[int(c) for c in '11011001001']
def step(xs):return [b ^ ((xs[j-1] if j>=1 else 0)|(xs[j-2] if j>=2 else 0)) for j,b in enumerate(xs)]
rows=[word]
for t in range(33):rows.append(step(rows[-1]))
assert rows[32]==word and rows[16]!=word
j=next(i for i in range(len(word)) if rows[16][i]!=word[i])
assert j>0 and rows[16][:j]==word[:j]
assert all(rows[t+16][j]==1-rows[t][j] for t in range(17))
assert all(rows[t+16][:j]==rows[t][:j] for t in range(17))
# Each column's4 bits are values at t,t+1,t+16,t+17.
def profile(w,t):return sum(w[(t+d)%32]<<k for k,d in enumerate([0,1,16,17]))
def bit(p,k):return (p>>k)&1
def pair(a,u):return a+16*u
def covers(a,u):
    return all((not bit(u,k) or (bit(a,k)^bit(a,k+1))) and
      (not (bit(a,k)^bit(a,k+1)) or bit(u,k) or bit(u,k+1)) for k in [0,2])
def children(a,u):
    for x,y in [(0,0),(0,1),(1,0),(1,1)]:
        b=x+2*(x^(bit(a,0)|bit(u,0)))+4*y+8*(y^(bit(a,2)|bit(u,2)))
        assert covers(b,a)
        yield pair(b,a)
seedA=[rows[t][j] for t in range(32)];seedU=[rows[t][j-1] for t in range(32)]
seeds={sign:sorted({pair(profile(seedA,t),profile(seedU,t)) for t in range(sign,32,2)}) for sign in [0,1]}
result={'word':'11011001001','P':16,'first_birth_index':j,'older_prefix':''.join(map(str,word[:j])),
 'birth_word':''.join(map(str,word[:j+1])),'target_sha256':hashlib.sha256(fixed.read_bytes()).hexdigest(),'classes':{}}
for parity in [0,1]:
    prev={s:None for s in seeds[parity]};origin={s:s for s in seeds[parity]};q=collections.deque(seeds[parity])
    level={s:0 for s in seeds[parity]};choice={s:0 for s in seeds[parity]}
    while q:
        st=q.popleft();a,u=st%16,st//16
        assert covers(a,u)
        for ch,nxt in enumerate(children(a,u)):
            if nxt not in prev:
                prev[nxt]=st;origin[nxt]=origin[st];level[nxt]=level[st]+1;choice[nxt]=ch;q.append(nxt)
    observations=[]
    for newer,older in [('A','u'),('b','A')]:
        aa=[int(c) for c in target[newer]['bits']];uu=[int(c) for c in target[older]['bits']]
        for t in range(parity,32,2):
            st=pair(profile(aa,t),profile(uu,t));path=None
            if st in prev:
                path=[st]
                while prev[path[-1]] is not None:path.append(prev[path[-1]])
                path.reverse()
            observations.append({'pair':newer+older,'time':t,'state':st,'path':path})
    result['classes'][parity]={'seeds':seeds[parity],'reachable':len(prev),'valid_cover_states':sum(covers(a,u) for a in range(16) for u in range(16)),
      'observations':observations,'all_target_observations_reached':all(x['path'] is not None for x in observations),
      'max_witness_steps':max(len(x['path'])-1 for x in observations if x['path']),
      'max_saturation_steps':max(level.values()),
      'rank_table':[level.get(s,0) for s in range(256)],
      'pred_table':[(prev[s] if prev[s] is not None else 0) if s in prev else 0 for s in range(256)],
      'choice_table':[choice.get(s,0) for s in range(256)],
      'witness_table':[next((t for t in range(parity,32,2) if pair(profile(seedA,t),profile(seedU,t))==s),0) for s in range(256)]}
(root/'abstract-closure.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({**{k:v for k,v in result.items() if k!='classes'},'classes':{s:{k:v for k,v in x.items() if k!='observations' and not k.endswith('_table')} for s,x in result['classes'].items()}},indent=2))
