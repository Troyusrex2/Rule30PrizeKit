"""Falsify the conjectured three-times-width separation horizon.
Short profiles are exact finite prefixes. Deduplication requires the proved
reader's acceptance for BOTH adjacent complete columns, never a tail guess.
"""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent
dfa=json.loads((root/'learned-reader.json').read_bytes())['dfa']
MAX=24;T=3*MAX;MASK=(1<<T)-1;NODE_CAP=2100000;SECONDS=150
def integrate(g,bit):
    x=g;s=1
    while s<T:x^=x<<s;s*=2
    return ((x<<1)&MASK)^(MASK if bit else 0)
def accepted(a,b,n):
    q=0
    for j in range(n):q=dfa['transitions'][q][(((a>>j)&1)<<1)|((b>>j)&1)]
    return q in dfa['accepting']
def first_difference(a,b,n):
    bound=1<<(n-1);mask=(1<<n)-1
    limit=min(bound,2000000)
    for t in range(limit):
        if ((a^b)>>(n-1))&1:return {'status':'different','first_difference_time':t,'exact_period_bound':bound}
        a=(a^((a<<1)|(a<<2)))&mask
        b=(b^((b<<1)|(b<<2)))&mask
    return {'status':'same_all_time_at_this_finite_width' if limit==bound else 'extension_cap',
            'checked':limit,'exact_period_bound':bound}
states={(0,0):0};reports=[];witness=None;stop='max_width';start=time.monotonic()
for n in range(1,MAX+1):
    new={};groups={};read_checks=0;cap=False
    for (u,v),word in states.items():
        if len(new)>NODE_CAP:stop='node_cap';cap=True;break
        if time.monotonic()-start>SECONDS:stop='time_cap';cap=True;break
        for bit in [0,1]:
            w=integrate(u|v,bit);initial=word|(bit<<(n-1));key=w&((1<<(3*n))-1)
            if key in groups:
                other=groups[key];read_checks+=1
                if not accepted(initial,other,n):
                    witness={'kind':'short_output_collision','width':n,'a_initial':initial,'b_initial':other,
                             'common_initial_time_bits':3*n,**first_difference(initial,other,n)}
                    cap=True;stop='witness';break
            else:groups[key]=initial
            pair=(v,w)
            if pair in new:
                other=new[pair];read_checks+=2
                if not (accepted(initial,other,n) and accepted(initial,other,n-1)):
                    witness={'kind':'pair_merge_not_certified','width':n,'a_initial':initial,'b_initial':other,
                             'common_initial_time_bits':T,**first_difference(initial,other,n)}
                    cap=True;stop='uncertified_merge';break
            else:new[pair]=initial
        if cap:break
    rec={'width':n,'processed_previous_states':len(states),'next_pair_states':len(new),
         'column_groups':len(groups),'reader_checks':read_checks,'complete':not cap,
         'seconds_total':round(time.monotonic()-start,3)}
    reports.append(rec);print(json.dumps(rec),flush=True)
    if cap:break
    states=new
out={'reports':reports,'stop_reason':stop,'witness':witness,'profile_time_bits':T,
     'node_cap':NODE_CAP,'seconds_cap':SECONDS,'seconds':round(time.monotonic()-start,3),
     'finite_only':True,'Lean_verified':False,'reader_completeness_proved':False,'full_problem_solved':False}
(root/'late-separation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
