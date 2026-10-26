"""Exhaustively test tiny temporal DFA observers on canonical white profiles.
An end-of-word output is allowed. Outside the finite valid data, behavior
is unconstrained. This tests only a bounded-state decoder template.
"""
from pathlib import Path
import json,time,itertools
import numpy as np
from numba import njit
r=Path(__file__).resolve().parent;START=time.monotonic()
C=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]];D={0,1,4,5}

def integral(x,b,P):
    y=x;s=1;mask=(1<<P)-1
    while s<P:y^=y<<s;s*=2
    return ((y<<1)&mask)^(mask if b else 0)

def graph(P):
    states=[(0,0,0)];index={states[0]:0};parents=[None];chosen={}
    for at,(u,v,d) in enumerate(states):
        drive=u|v
        if d in D:
            if drive not in chosen:chosen[drive]=at
            else:assert states[chosen[drive]][1]==v
        if drive.bit_count()%2==0:
            for b in range(2):
                nxt=(v,integral(drive,b,P),C[d][b])
                if nxt not in index:index[nxt]=len(states);states.append(nxt);parents.append((at,b))
        assert len(states)<1500000
    def word(i):
        out=[]
        while parents[i] is not None:i,b=parents[i];out.append(b)
        return out[::-1]
    data=[]
    for profile,i in chosen.items():
        data.append({'clock':P,'OR_profile':profile,'target':states[i][1]&1,'parent_initial':word(i)})
    return data,len(states)

@njit(cache=False)
def filter_models(S,active,profiles,clocks,targets):
    badfirst=np.full(len(active),-1,np.int32);badsecond=np.full(len(active),-1,np.int32)
    for model in range(len(active)):
        if not active[model]:continue
        trans=np.empty(2*S,np.int32);v=model
        for i in range(2*S):trans[i]=v%S;v//=S
        labels=np.full(S,-1,np.int8);seen=np.full(S,-1,np.int32)
        for row in range(len(profiles)):
            state=0;word=profiles[row]
            for t in range(clocks[row]):
                state=trans[2*state+int((word>>t)&np.uint64(1))]
            label=targets[row]
            if labels[state]>=0 and labels[state]!=label:
                badfirst[model]=seen[state];badsecond[model]=row;active[model]=False;break
            labels[state]=label;seen[state]=row
    return active,badfirst,badsecond

def literal(data):
    P=data['clock'];state=data['parent_initial'].copy();g=[];rr=[]
    for t in range(P):
        g.append(state[-1] if state else 0)
        rr.append((state[-1] if state else 0)|(state[-2] if len(state)>1 else 0))
        nxt=[];a=b=0
        for x in state:nxt.append((30>>(4*x+2*a+b))&1);b,a=a,x
        state=nxt
    assert state==data['parent_initial']
    assert sum(v<<i for i,v in enumerate(rr))==data['OR_profile'] and g[0]==data['target']

controls=0
for P in [2,4,8]:
    for drive in range(1<<P):
        if drive.bit_count()%2:continue
        for b in [0,1]:
            out=integral(drive,b,P)
            assert all(((out>>((t+1)%P))&1)==(((out>>t)&1)^((drive>>t)&1)) for t in range(P))
            controls+=1
all_data=[];reports=[];witnesses={S:{} for S in range(1,5)}
active={S:np.ones(S**(2*S),dtype=np.bool_) for S in range(1,5)}
for P in [2,4,8,16,32,64]:
    data,states=graph(P);all_data+=data
    profiles=np.array([x['OR_profile'] for x in all_data],dtype=np.uint64)
    clocks=np.array([x['clock'] for x in all_data],dtype=np.int32)
    targets=np.array([x['target'] for x in all_data],dtype=np.int8)
    counts={}
    for S in range(1,5):
        active[S],a,b=filter_models(S,active[S],profiles,clocks,targets)
        for model in np.flatnonzero(a>=0):witnesses[S][int(model)]=[int(a[model]),int(b[model])]
        counts[S]=int(active[S].sum())
    for x in data:literal(x)
    reports.append({'clock':P,'product_states':states,'samples':len(all_data),'surviving_DFA_tables':counts})
    print(json.dumps(reports[-1]),flush=True)
    if not any(x.any() for x in active.values()):break
out={'controls':controls,'reports':reports,'samples':all_data,'counterexample_pairs_by_table':witnesses,
     'all_DFA_up_to_four_states_refuted':not any(x.any() for x in active.values()),
     'full_canonical_observer_refuted':False,'Lean_verified':False,'full_problem_solved':False,
     'seconds':round(time.monotonic()-START,3)}
(r/'temporal-dfa-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['samples','counterexample_pairs_by_table']}),flush=True)
