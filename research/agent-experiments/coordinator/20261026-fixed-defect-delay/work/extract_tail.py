from pathlib import Path
from collections import deque
import json
root=Path(__file__).resolve().parent
P=8;B=1<<P;mask=B-1
def integral(g,bit):
    x=g;s=1
    while s<P:x^=x<<s;s*=2
    return ((x<<1)&mask)^(mask if bit else 0)
def derivative(x):return x^((x>>1)|((x&1)<<(P-1)))
out=[[] for _ in range(B*B)];pred=[[] for _ in range(B*B)]
for u in range(B):
    for v in range(B):
        g=u|v
        if g.bit_count()%2:continue
        for bit in (0,1):
            j=v*B+integral(g,bit);out[u*B+v].append(j);pred[j].append(u*B+v)
degree=list(map(len,pred));q=deque(i for i,d in enumerate(degree) if d==0);dead=set(q)
while q:
    for j in out[q.popleft()]:
        degree[j]-=1
        if degree[j]==0:dead.add(j);q.append(j)
example=json.loads((root/'viable-split-probe.json').read_bytes())['reports'][-1]['example']
u,v=example['seed_common'];seen={};chain=[];node=u*B+v
while node not in seen:
    seen[node]=len(chain);chain.append(node)
    node=min(i for i in pred[node] if i not in dead)
mu=seen[node];cycle=len(chain)-mu
tail_pre=[i%B for i in chain[:mu]];tail_period=[i%B for i in chain[mu:]]
a=integral(u|v,0);b=a^mask
left_a=[a];left_b=[b]
pa=pb=v
for abit,bbit in example['extension_initials']:
    na=integral(pa|a,abit);nb=integral(pb|b,bbit)
    pa,a=a,na;pb,b=b,nb
    left_a.append(a);left_b.append(b)
prefix_a=list(reversed(left_a))+tail_pre;prefix_b=list(reversed(left_b))+tail_pre
M=len(prefix_a);L=len(tail_period)
def at(prefix,k):return prefix[k] if k<M else tail_period[(k-M)%L]
for prefix in [prefix_a,prefix_b]:
    for k in range(M+L):
        assert derivative(at(prefix,k))==(at(prefix,k+1)|at(prefix,k+2)),(k,at(prefix,k))
assert prefix_a[0]==prefix_b[0] and (prefix_a[4]^prefix_b[4])==255
assert all(at(prefix_a,k)==at(prefix_b,k) for k in range(5,M+L+2))
white={0};todo=[0]
while todo:
    for j in out[todo.pop()]:
        if j not in white:white.add(j);todo.append(j)
assert u*B+v not in white
result={'temporal_clock':P,'a_prefix':prefix_a,'b_prefix':prefix_b,
        'shared_tail':tail_period,'prefix_length':M,'tail_spatial_period':L,
        'common_seed':example['seed_common'],'source_depth':4,'shared_from_depth':5,
        'head_profile':prefix_a[0],'source_delta_profile':255,
        'cyclic_profile_equations_checked':2*(M+L),
        'white_clock8_reachable':False,'not_a_right_bounded_example':True,
        'Lean_verified':False,'full_problem_solved':False}
(root/'explicit-tail.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result),flush=True)
