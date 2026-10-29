"""Independent stdlib regeneration of the two finite graph certificates."""
from pathlib import Path
from collections import deque
import json,re,sys,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'data'))
from graph_probe import build
start=time.monotonic();info,nexts,_=build(5);N=7776
core={v for c in info['components'] for v in (c['states'] or [])};assert len(core)==9
reverse=[[] for _ in range(N)];pending=[0]*N
for s in range(N):
    for t in nexts:
        if t[s]>=0:pending[s]+=1;reverse[t[s]].append(s)
dead=[0]*N;q=deque(s for s in range(N) if not pending[s])
while q:
    s=q.popleft();dead[s]=1+max([dead[t[s]] for t in nexts if t[s]>=0]+[0])
    for v in reverse[s]:
        pending[v]-=1
        if not pending[v]:q.append(v)
ranks=[None]*N;visiting=set()
def rank(s):
    if dead[s] or s in core:ranks[s]=0;return 0
    if ranks[s] is not None:return ranks[s]
    assert s not in visiting;visiting.add(s)
    ranks[s]=1+max(rank(t[s]) for t in nexts if t[s]>=0 and not dead[t[s]])
    visiting.remove(s);return ranks[s]
for s in range(N):rank(s)
g={s:next(t[s] for t in nexts if t[s] in core) for s in sorted(core)}
recorded=json.loads((ROOT/'data/CERTIFICATE.json').read_text())
assert recorded['dead_ranks']==dead and recorded['transient_ranks']==ranks and recorded['core']==sorted(core)
assert {int(k):v for k,v in recorded['successor'].items()}==g
source=(ROOT/'replay/sources/Ruliology/CellularAutomata/Rule30ResetFreeCore.lean').read_text(encoding='utf-8')
for name,values in [('deadData',dead),('rankData',ranks)]:
    actual=int(re.search(r'def '+name+r' : Nat := (0x[0-9a-f]+)',source).group(1),16)
    assert actual==sum(v<<(8*i) for i,v in enumerate(values)),name
actual_core=json.loads(re.search(r'def coreStates : List Nat := (\[[^\n]+\])',source).group(1));assert actual_core==sorted(core)
successor_part=source[source.index('def successor (s : Nat)'):source.index('def graph : Ranked')]
assert {int(a):int(b) for a,b in re.findall(r'if s=(\d+) then (\d+)',successor_part)}==g
_,edges,_=build(3);reach={sum(2*((b>>i)&1)*6**i for i in range(3)) for b in range(8)};q=deque(reach)
while q:
    s=q.popleft()
    for t in edges:
        v=t[s]
        if v>=0 and v not in reach:reach.add(v);q.append(v)
source=(ROOT/'replay/sources/Ruliology/CellularAutomata/Rule30ResetFreeThree.lean').read_text(encoding='utf-8')
assert json.loads(re.search(r'def reachableStates : List Nat := (\[[^\n]+\])',source).group(1))==sorted(reach)
assert len(reach)==20
for s in reach:
    for t in edges:
        if t[s]>=0:assert t[s] in reach and (t[s]!=0 or s==0)
def finite_step(w):
    bits=[0]+[(w>>i)&1 for i in range(w.bit_length()+3)]
    return sum(((30>>(4*bits[k+1]+2*bits[k]+bits[k-1]))&1)<<(k-1) for k in range(1,len(bits)-1))
def finite_reset(w):
    bits=[0]+[(w>>i)&1 for i in range(w.bit_length()+2)];zeros=[i for i,b in enumerate(bits) if not b]
    return any((b-a-1)%3==1 for a,b in zip(zeros,zeros[1:]))
assert finite_step(3)==6 and finite_step(6)==13
assert not finite_reset(3) and not finite_reset(6) and finite_reset(13)
r={'all_data_regenerated':True,'ranked_graph_vertices':N,'core_states':len(core),'max_dead_rank':max(dead),'max_transient_rank':max(ranks),'finite_three_reachable_states':len(reach),'sharpness_literal_replayed':True,'seconds':time.monotonic()-start,'kernel_verified':False}
print(json.dumps(r))
