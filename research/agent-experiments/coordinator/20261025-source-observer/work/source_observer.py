"""Exact multi-output F2 observers on frozen pair-difference coefficient fields.

This searches for a basis-vector row-space certificate, not just a path.
No finite census asserts the unbounded observability criterion needed for P1.
"""
from pathlib import Path
import json,random,time
root=Path(__file__).resolve().parent;start=time.monotonic()
def advance(a,rule):
    if rule==30:return (a<<1)^(a|(a>>1))
    if rule==210:return (a<<1)^((a>>1)&~a)
    raise ValueError(rule)
def parity(a):return a.bit_count()&1
def observer(TA,TB,rule=30,cap=None):
    assert TA>TB>=0
    W=TA;N=cap if cap is not None else 4*W+64
    origin=W+N+4;spatial_mask=(1<<(2*origin+1))-1
    a=b=1<<origin
    for _ in range(TA):a=advance(a,rule)&spatial_mask
    for _ in range(TB):b=advance(b,rule)&spatial_mask
    delta=((a^b)>>(origin-W))&((1<<(2*W+1))-1)
    assert delta&1
    initial_a=a;initial_b=b
    vectors=[1<<i for i in range(2*W+1)];lo=-W
    basis={};observations=[];actual=[];first_difference=None
    result=None
    for t in range(N+1):
        row=vectors[-lo];syndrome=(a>>origin&1)^(b>>origin&1)
        assert parity(row&delta)==syndrome,(rule,TA,TB,t)
        observations.append(row);actual.append(syndrome)
        if syndrome and first_difference is None:first_difference=t
        v=row;comb=1<<t
        while v:
            p=v.bit_length()-1
            if p in basis:v^=basis[p][0];comb^=basis[p][1]
            else:basis[p]=(v,comb);break
        v=1;comb=0
        while v:
            p=v.bit_length()-1
            if p not in basis:break
            v^=basis[p][0];comb^=basis[p][1]
        if v==0:
            rowsum=0;actualsum=0
            for j in range(t+1):
                if comb>>j&1:rowsum^=observations[j];actualsum^=actual[j]
            assert rowsum==1 and actualsum==1
            result={'observed_through':t,'rank':len(basis),'certificate_times':[j for j in range(t+1) if comb>>j&1],
                    'certificate_weight':comb.bit_count(),'actual_output_parity':actualsum}
            break
        if t==N:break
        L=len(vectors);new=[]
        for i in range(L+2):
            p=lo-1+i
            left=vectors[i-2] if 0<=i-2<L else 0
            center=vectors[i-1] if 0<=i-1<L else 0
            right=vectors[i] if i<L else 0
            bc=(b>>(p+1+origin))&1;ac=(a>>(p+origin))&1
            cc=(1^bc) if rule==30 else bc
            rc=1^ac
            new.append(left^(center if cc else 0)^(right if rc else 0))
        vectors=new;lo-=1
        a=advance(a,rule)&spatial_mask;b=advance(b,rule)&spatial_mask
    return {'rule':rule,'TA':TA,'TB':TB,'width':2*W+1,'cap':N,
            'first_actual_center_disagreement':first_difference,'rank':len(basis),'certificate':result,
            'unresolved':result is None,'center_identity_controls':len(actual)}

# Independent truth-table check of both exact pair-difference identities.
controls=0
for rule in (30,210):
    def g(c,r):return c|r if rule==30 else (1^c)&r
    for a in range(8):
        for b in range(8):
            al,ac,ar=(a>>2)&1,(a>>1)&1,a&1
            bl,bc,br=(b>>2)&1,(b>>1)&1,b&1
            lhs=al^g(ac,ar)^bl^g(bc,br)
            cc=(1^br) if rule==30 else br
            rhs=(al^bl)^((ac^bc)*cc)^((ar^br)*(1^ac))
            assert lhs==rhs;controls+=1

pairs=[(a,b) for a in range(1,33) for b in range(a)]
pairs += [(a,b) for a in (48,64,96,128) for b in (0,1,a//2,a-2,a-1)]
records=[];stop=None
with (root/'source-observer.partial.jsonl').open('w',encoding='utf-8') as log:
    for rule in (30,210):
        selected=pairs if rule==30 else [(a,b) for a in range(1,9) for b in range(a)]
        for a,b in selected:
            if time.monotonic()-start>230:stop='internal_time_budget';break
            rec=observer(a,b,rule);records.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
        print(json.dumps({'rule_done':rule,'tested':sum(r['rule']==rule for r in records),
                          'edge_unit_recovered':sum(r['rule']==rule and not r['unresolved'] for r in records),
                          'elapsed_seconds':time.monotonic()-start}),flush=True)
        if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
 'local_truth_table_controls':controls,'records':records,'stop':stop,'elapsed_seconds':time.monotonic()-start,
 'scope':'Frozen exact pair-difference fields of canonical time shifts. A found observer is a finite multi-output source certificate. Unresolved caps are unknown. No uniform observer or unbounded separation theorem has been established.'}
(root/'source-observer.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'unresolved_rule30':[{k:r[k] for k in ['TA','TB','cap','rank','first_actual_center_disagreement']} for r in records if r['rule']==30 and r['unresolved']][:8],
 'controls':controls,'stop':stop,'elapsed_seconds':out['elapsed_seconds']}))
