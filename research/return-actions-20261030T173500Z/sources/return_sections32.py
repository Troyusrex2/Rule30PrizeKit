"""Bounded new route: equal-length fixed prefixes of T^P with identical
positive return-section words would give a genuine bounded-defect pair.
P=32 only; 200 levels, 10000 states/level, 8-second total cap.
No merge is not a proof for all P. Uses PositiveAutomaton's exact tables.
"""
from pathlib import Path
import time,json
R=Path(__file__).resolve().parent;start=time.monotonic();results=[]
def section(word,bit):
    sections=[];b=bit
    for q in reversed(word):
        sections.append(2 if b else (1 if q==2 else 0))
        b^=(q!=0)
    return tuple(reversed(sections)),b
for P in [32]:
    root=(0,)*P;state,output=section(root,1);assert output==1
    current={state:(1,)};seen={};levels=[];merge=None;status='level_cap'
    for depth in range(1,201):
        key=frozenset(current)
        if key in seen:
            status='state-set cycle without merges';break
        seen[key]=depth
        alive=sum(sum(q!=0 for q in word)%2==0 for word in current)
        levels.append(dict(depth=depth,states=len(current),alive=alive))
        if len(current)>10000 or time.monotonic()-start>8:
            status='resource_cap';break
        nxt={}
        for word,path in current.items():
            if sum(q!=0 for q in word)%2:continue
            for bit in [0,1]:
                target,out=section(word,bit);assert out==bit
                newpath=path+(bit,)
                if target in nxt and nxt[target]!=newpath:
                    merge=dict(prefix_a=list(nxt[target]),prefix_b=list(newpath),return_section=list(target),depth=depth+1)
                    break
                nxt[target]=newpath
            if merge:break
        if merge:status='MERGE';break
        current=nxt
    result=dict(P=P,status=status,levels=levels,merge=merge)
    if status=='state-set cycle without merges':result['cycle_start_depth']=seen[key];result['cycle_detected_depth']=depth
    results.append(result)
    if merge or time.monotonic()-start>8:break
(R/'RETURN_SECTIONS.json').write_text(json.dumps(dict(results=results,seconds=time.monotonic()-start,
    proof_obligation='All powers have no two distinct same-length fixed black-edge prefixes with the same return section. Equality of words certifies equality of actions, but bounded experiments cannot prove all powers.'),indent=2)+'\n')
print(json.dumps(dict(results=[dict(P=r['P'],status=r['status'],last=r['levels'][-1],merge=r['merge']) for r in results],seconds=round(time.monotonic()-start,3))))
