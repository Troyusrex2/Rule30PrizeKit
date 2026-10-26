"""Exact all-width, temporal-depth-two test with genuine white closure.

No unbounded temporal claim: if a witness exists it satisfies Common only
at times 0,1,2 and loses Subset at time 1. The automaton scans initial cells.
"""
from pathlib import Path
from collections import deque
from functools import lru_cache
import json,time

root=Path(__file__).resolve().parent
T=2;memory=2*T+1
def unpack(x):return ((x>>0)&1,(x>>1)&1,(x>>2)&1)
def pack(a,b,h):return a+2*b+4*h
def good(x,y):
    a,b,h=unpack(x);c,d,k=unpack(y)
    return (a^b)*k==h*(c^d)
def bad(x):
    a,b,h=unpack(x);return bool(h and not (a^b))
def step3(p,q,r):
    a,b,h=unpack(r);ap,bp,hp=unpack(q);aq,bq,hq=unpack(p)
    return pack(a^(ap|aq),b^(bp|bq),h^((1-bq)*hp)^((1-ap)*hq))
alphabet=tuple(x for x in range(8) if not bad(x))
@lru_cache(None)
def transition(history,x):
    row=list(history)+( [x] );seen=False
    for t in range(T+1):
        if not good(row[-2],row[-1]):return None
        if t==1:seen=bad(row[-1])
        if t<T:row=[step3(row[j-2],row[j-1],row[j]) for j in range(2,len(row))]
    return history[1:]+(x,),seen
initial=((0,)*memory,False)
parent={initial:None};queue=deque([initial]);edges=0;answer=None;start=time.monotonic()
def close(state):
    hist,seen=state
    for _ in range(memory):
        tr=transition(hist,0)
        if tr is None:return None
        hist,now=tr;seen|=now
    assert hist==(0,)*memory
    return seen
while queue:
    state=queue.popleft()
    if close(state):answer=state;break
    hist,seen=state
    for x in alphabet:
        tr=transition(hist,x);edges+=1
        if tr is None:continue
        nh,now=tr;n=(nh,seen or now)
        if n not in parent:parent[n]=(state,x);queue.append(n)
result={'temporal_depth':T,'memory_symbols':memory,'initial_alphabet':list(alphabet),
        'states_discovered':len(parent),'edges_examined':edges,'seconds':time.monotonic()-start,
        'whole_halfline_Common_assumed_only_at':[0,1,2],
        'all_time_Common_counterexample':False,'full_problem_solved':False}
if answer is not None:
    letters=[];n=answer
    while parent[n] is not None:n,x=parent[n];letters.append(x)
    letters.reverse()
    rows=[[sum(unpack(x)[k]<<j for j,x in enumerate(letters)) for k in range(3)]]
    # Independent whole-integer update; includes every newly created cell.
    for t in range(T+2):
        a,b,h=rows[-1]
        rows.append([a^((a<<1)|(a<<2)),b^((b<<1)|(b<<2)),
                     h^((~(b<<2))&(h<<1))^((~(a<<1))&(h<<2))])
    audits=[]
    for t,(a,b,h) in enumerate(rows):
        d=a^b;width=max(a.bit_length(),b.bit_length(),h.bit_length())+1
        common_bad=[j for j in range(width) if ((d>>j)&1)*((h>>(j+1))&1)!=((h>>j)&1)*((d>>(j+1))&1)]
        subset_bad=[j for j in range(width) if ((h&~d)>>j)&1]
        audits.append({'time':t,'a':a,'b':b,'h':h,'common_failures':common_bad,'subset_failures':subset_bad})
        if t:
            old=rows[t-1]
            for j in range(width):
                for k in [0,1]:
                    v=4*((old[k]>>j)&1)+2*((old[k]>>(j-1))&1 if j else 0)+((old[k]>>(j-2))&1 if j>=2 else 0)
                    assert ((rows[t][k]>>j)&1)==((30>>v)&1)
                hp=(old[2]>>(j-1))&1 if j else 0;hq=(old[2]>>(j-2))&1 if j>=2 else 0
                ap=(old[0]>>(j-1))&1 if j else 0;bq=(old[1]>>(j-2))&1 if j>=2 else 0
                assert ((h>>j)&1)==((old[2]>>j)&1)^((1-bq)*hp)^((1-ap)*hq)
    assert not audits[0]['subset_failures'] and audits[1]['subset_failures']
    assert all(not x['common_failures'] for x in audits[:T+1])
    result.update(status='counterexample',input_symbols=letters,rows=audits,literal_audit=True)
else:
    result.update(status='no_finite_white_counterexample',exhaustive_reachable_states=True)
    # A positive result would require an independently audited, kernel-checked bridge.
    result['kernel_checked']=False
(root/'two-step-closed-transducer.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
