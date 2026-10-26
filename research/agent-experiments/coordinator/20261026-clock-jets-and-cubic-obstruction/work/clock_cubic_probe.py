"""Test cubic parent recovery on complete fixed-clock white profile graphs.
There is no spatial word-length cut-off. The clock is bounded. A negative
span witness can refute the proposed uniform cubic decoder, not the observer.
"""
from pathlib import Path
import json,time,itertools
r=Path(__file__).resolve().parent;START=time.monotonic();reports=[];negative=None
C=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]];D={0,1,4,5}
def integral(x,b,P):
    mask=(1<<P)-1;y=0;s=b
    for t in range(P):
        y|=s<<t;s^=(x>>t)&1
    assert s==b
    return y
def reduce(v,basis):
    while v:
        p=v.bit_length()-1
        if p not in basis:return v
        v^=basis[p]
    return 0
for P in [2,4,8,16,32]:
    begin=time.monotonic();mask=(1<<P)-1
    states=[(0,0,0)];index={states[0]:0};parents=[None];at=0;chosen={};collision=None
    while at<len(states):
        u,v,d=states[at]
        if d in D:
            out=u|v
            if out not in chosen:chosen[out]=at
            elif states[chosen[out]][1]!=v:collision=[chosen[out],at]
        drive=u|v
        if drive.bit_count()%2==0:
            for b in range(2):
                w=integral(drive,b,P);st=(v,w,C[d][b])
                if st not in index:index[st]=len(states);states.append(st);parents.append((at,b))
        at+=1
        assert len(states)<1500000
    assert collision is None,(P,collision)
    ids=list(chosen.values());M=len(ids)
    obs=[sum(((states[i][0]|states[i][1])>>t&1)<<j for j,i in enumerate(ids)) for t in range(P)]
    target=sum((states[i][1]&1)<<j for j,i in enumerate(ids))
    basis={M-1:(1<<M)-1};layers=[]
    for degree in range(1,4):
        previous=list(basis.values())
        for b in previous:
            for f in obs:
                v=reduce(b&f,basis)
                if v:basis[v.bit_length()-1]=v
        residual=reduce(target,basis)
        layers.append({'degree':degree,'rank':len(basis),'parent_bit_recoverable':not residual})
        if not residual:break
    def word(i):
        out=[]
        while parents[i] is not None:i,b=parents[i];out.append(b)
        return out[::-1]
    rec={'clock':P,'closed_product_states':len(states),'canonical_OR_profiles':M,'layers':layers,
         'maximum_representative_length':max(len(word(i)) for i in ids),
         'closed':True,'seconds':round(time.monotonic()-begin,3)}
    reports.append(rec);print(json.dumps(rec),flush=True)
    if residual:
        # Dual functional kills the whole computed cubic span, sees the target.
        dual=1<<(residual.bit_length()-1)
        for p,b in sorted(basis.items()):
            if (b&dual).bit_count()%2:dual^=1<<p
        assert all((b&dual).bit_count()%2==0 for b in basis.values())
        assert (target&dual).bit_count()%2==1
        witness=[{'initial_parent':word(ids[j]),'older_profile':states[ids[j]][0],
                  'newer_profile':states[ids[j]][1],'OR_profile':states[ids[j]][0]|states[ids[j]][1]}
                 for j in range(M) if (dual>>j)&1]
        negative={'clock':P,'witness':witness,'witness_size':len(witness),
                  'maximum_parent_length':max(len(x['initial_parent']) for x in witness)}
        print(json.dumps({'negative_cubic_span_witness':len(witness),'clock':P}),flush=True)
    out={'reports':reports,'negative_witness':negative,'finite_clocks_only':True,
         'Lean_verified':False,'canonical_observer_refuted':False,'full_problem_solved':False}
    (r/'clock-cubic-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    if negative:break
