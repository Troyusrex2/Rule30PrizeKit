"""Falsify a structural alternative: a nonzero golden difference is alternating.
All profiles cover their complete proved power-of-two period, not a tail.
"""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent
dfa=json.loads((root/'learned-reader.json').read_bytes())['dfa']
def integral(g,bit,P):
    mask=(1<<P)-1;x=g;s=1
    while s<P:x^=x<<s;s*=2
    return ((x<<1)&mask)^(mask if bit else 0)
def raw(a,b,n):
    q=0
    for j in range(n):q=dfa['transitions'][q][(((a>>j)&1)<<1)|((b>>j)&1)]
    return q
states={(0,0):0};oldP=1;records=[];counter=None;sinkexample=None;start=time.monotonic()
for n in range(1,12):
    P=1<<(n-1);mask=(1<<P)-1;new={}
    for (u,v),word in states.items():
        if n>1:u|=u<<oldP;v|=v<<oldP
        for bit in [0,1]:
            w=integral(u|v,bit,P);new.setdefault((v,w),word|(bit<<(n-1)))
    states=new;oldP=P;profiles={v:word for (_,v),word in states.items()};items=list(profiles.items())
    tested=0;golden=0;sinkgolden=0
    for j,(a,aw) in enumerate(items):
        for b,bw in items[j+1:]:
            delta=a^b;shift=(delta>>1)|((delta&1)<<(P-1));tested+=1
            if delta&shift:continue
            golden+=1;phase2=(delta>>2)|((delta&3)<<(max(P-2,0))) if P>=2 else delta
            q=raw(aw,bw,n)
            if q==15:sinkgolden+=1
            example={'width':n,'a_initial':aw,'b_initial':bw,'dfa_state':q,
                         'period_bound':P,'delta_hex':hex(delta),'delta_golden':True,
                         'alternating_or_zero':P<2 or phase2==delta}
            if q==15 and sinkexample is None:sinkexample=example
            if P>=2 and phase2!=delta:
                counter=example
                break
        if counter:break
    rec={'width':n,'distinct_profiles':len(items),'distinct_pairs_tested':tested,
         'golden_pairs':golden,'sink_golden_pairs':sinkgolden,'complete':counter is None}
    records.append(rec);print(json.dumps(rec),flush=True)
    if counter:break
out={'records':records,'counterexample':counter,'sink_golden_example':sinkexample,'seconds':round(time.monotonic()-start,3),
     'finite_only':True,'Lean_verified':False,'full_problem_solved':False}
(root/'golden-difference.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
