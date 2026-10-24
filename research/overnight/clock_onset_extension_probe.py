"""Falsify arbitrary-distance propagation beyond the proved local clock lemma.

An infinite half-clock tail is permitted. A counterexample must not be called
a finite-tail counterexample. Exact finite profiles are checked by whole-row
scalar evolution on a sufficient causal cone before they are reported.
"""
from collections import deque
import json
from pathlib import Path
import time


def integrate(rhs,clock):
    if rhs.bit_count()%2:return None
    value=rhs;shift=1
    while shift<clock:value^=value<<shift;shift*=2
    return (value<<1)&((1<<clock)-1)


def live_profiles(half):
    mask=(1<<half)-1;n=1<<(2*half)
    edges=[[] for _ in range(n)];pred=[[] for _ in range(n)]
    for key in range(n):
        b,c=key&mask,key>>half;a=integrate(b|c,half)
        if a is None:continue
        for value in (a,a^mask):
            target=value|(b<<half);edges[key].append(target);pred[target].append(key)
    degree=list(map(len,pred));live=bytearray([1])*n
    queue=deque(i for i,d in enumerate(degree) if not d)
    while queue:
        key=queue.popleft();live[key]=0
        for target in edges[key]:
            degree[target]-=1
            if not degree[target]:queue.append(target)
    return [i for i in range(n) if live[i]],pred,live


def probe(half,limit=500000):
    began=time.monotonic();clock=2*half;mask=(1<<clock)-1;small=(1<<half)-1
    roots,pred,live=live_profiles(half)
    parents={};rootkeys={};queue=deque()
    repeat=lambda x:x|(x<<half)
    for root in roots:
        key=repeat(root&small)|(repeat(root>>half)<<clock)
        parents[key]=None;rootkeys[key]=root;queue.append(key)
    counter=None
    def is_small(x):return x&small==x>>half
    while queue and len(parents)<limit:
        key=queue.popleft();b,c=key&mask,key>>clock;a=integrate(b|c,clock)
        if a is None:continue
        for value in (a,a^mask):
            target=value|(b<<clock)
            if target in parents:continue
            parents[target]=key;queue.append(target)
            if is_small(value) and not is_small(b):counter=target;break
        if counter is not None:break
    result={'finite_experiment_only':True,'Lean_verified':False,'full_problem_claim':False,
            'finite_tail_counterexample':False,'half_clock':half,'clock':clock,
            'infinite_tail_roots':len(roots),'visited_profile_pairs':len(parents),
            'exhausted':not queue,'state_guard_hit':len(parents)>=limit,
            'counterexample_found':counter is not None}
    if counter is not None:
        key=counter;prefix=[]
        while parents[key] is not None:
            prefix.append(key&mask);key=parents[key]
        root=rootkeys[key];seen={};tail=[]
        while root not in seen:
            seen[root]=len(tail);tail.append(repeat(root&small))
            root=min(p for p in pred[root] if live[p])
        cut=seen[root];prefix+=tail[:cut];periodic=tail[cut:]
        def profile(k):return prefix[k] if k<len(prefix) else periodic[(k-len(prefix))%len(periodic)]
        horizon=4*clock;window=len(prefix)+2*len(periodic)+4
        row=sum((profile(k)&1)<<k for k in range(2*horizon+window+2))
        for t in range(horizon):
            for k in range(window):assert (row>>k)&1==(profile(k)>>(t%clock))&1
            row^=(row>>1)|(row>>2)
        result.update(prefix_profiles=prefix,periodic_tail_profiles=periodic,
                      independent_scalar_cells_checked=horizon*window,
                      prefix_column_count=len(prefix),all_checks_passed=True)
    result['seconds']=round(time.monotonic()-began,3)
    return result


if __name__=='__main__':
    result=probe(8)
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(result))
