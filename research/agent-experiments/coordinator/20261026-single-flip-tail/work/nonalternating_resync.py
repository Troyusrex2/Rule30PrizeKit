"""Test whether a common nonconstant right profile prevents later resynchronization.
Seeds need only the stated local admissibility, not white-tail reachability.
A counterexample would refute that local generalization, not the reader.
"""
from pathlib import Path
import json,time,sys
from collections import deque
root=Path(__file__).resolve().parent;reports=[]
viable_mode=True
def derivative(x,P):return x^((x>>1)|((x&1)<<(P-1)))
def integral(g,bit,P):
    mask=(1<<P)-1;x=g;s=1
    while s<P:x^=x<<s;s*=2
    return ((x<<1)&mask)^(mask if bit else 0)
def viable_pairs(P):
    B=1<<P;out=[[] for _ in range(B*B)];indegree=[0]*(B*B)
    for u in range(B):
        for v in range(B):
            g=u|v
            if g.bit_count()%2:continue
            for bit in [0,1]:
                w=integral(g,bit,P);j=v*B+w
                out[u*B+v].append(j);indegree[j]+=1
    queue=deque(i for i,d in enumerate(indegree) if d==0);removed=set(queue)
    while queue:
        for j in out[queue.popleft()]:
            indegree[j]-=1
            if indegree[j]==0:removed.add(j);queue.append(j)
    return {(i//B,i%B) for i in range(B*B) if i not in removed}
for P in [2,4,8]:
    start=time.monotonic();mask=(1<<P)-1;states=[];parents=[];ids={};seeds=0
    viable=viable_pairs(P) if viable_mode else None
    for u in range(1<<P):
        for v in range(1,mask):
            if viable is not None and (u,v) not in viable:continue
            if u&~derivative(v,P):continue
            if (u|v).bit_count()%2:continue
            w=integral(u|v,0,P);state=(v,w,v,w^mask)
            if state not in ids:
                ids[state]=len(states);states.append(state)
                parents.append({'seed_common':[u,v],'source_initial':[0,1]});seeds+=1
    at=0;found=None;stop=None;edges=0
    while at<len(states):
        if len(states)>250000:stop='node_cap';break
        if time.monotonic()-start>60:stop='time_cap';break
        u,v,up,vp=states[at]
        if v==vp and u!=up:
            shift2=((v>>2)|((v&3)<<(P-2))) if P>=2 else v
            if shift2!=v:found=at;stop='nonalternating_resynchronization';break
        ga,gb=u|v,up|vp
        if ga.bit_count()%2==0 and gb.bit_count()%2==0:
            for a in [0,1]:
                for b in [0,1]:
                    w=integral(ga,a,P);wp=integral(gb,b,P);nxt=(v,w,vp,wp);edges+=1
                    if nxt not in ids:
                        ids[nxt]=len(states);states.append(nxt);parents.append((at,a,b))
        at+=1
    example=None
    if found is not None:
        j=found;extensions=[]
        while not isinstance(parents[j],dict):j,a,b=parents[j];extensions.append([a,b])
        example={**parents[j],'extension_initials':list(reversed(extensions)),
                 'synchronized_pair_state':states[found],'seed_right_bounded_verified':False}
        example['seed_has_infinite_clock_admissible_right_extension']=viable_mode
    rec={'temporal_clock':P,'seed_states':seeds,'states':len(states),'processed':at,
         'edges':edges,'closed':stop is None,'stop_reason':stop,'example':example,
         'viable_common_pairs':len(viable) if viable is not None else None,
         'seconds':round(time.monotonic()-start,3)}
    reports.append(rec);print(json.dumps(rec),flush=True)
    (root/'nonalternating-resync.json').write_text(json.dumps({'reports':reports,'Lean_verified':False,
        'reader_completeness_proved':False,'full_problem_solved':False},indent=2)+'\n',encoding='utf-8')
    if example:break
