"""Falsify finite-history backward recombination using exact future pair traces.
Finite equality alone is not an all-time rectangle proof.
"""
from pathlib import Path
import hashlib,itertools,json,time
ROOT=Path(__file__).resolve().parent
width=8;steps=128
def step(a):return (a<<2) ^ ((a<<1)|a)
# At time t, bit p+t is the physical cell p. This is a moving storage origin.
rows=[]
for initial in range(1<<width):
    row=initial;trace=[]
    for t in range(steps+2):trace.append(row);row=step(row)
    rows.append(trace)
seen={};collisions=[];pair_count=0
for a,b in itertools.combinations(range(1<<width),2):
    current_delta=rows[a][1]^rows[b][1]
    current_common=rows[a][1]&rows[b][1]
    h=hashlib.sha256()
    for t in range(1,steps+2):
        q=rows[a][t]^rows[b][t]
        h.update(q.to_bytes((width+2*t+7)//8,'little'))
    # Require the present four rows to be a pointwise recombination too.
    key=(h.digest(),current_delta,current_common)
    pair_count+=1
    if key in seen:
        c,d=seen[key]
        assert all((rows[a][t]^rows[b][t])==(rows[c][t]^rows[d][t]) for t in range(1,steps+2))
        previous_rectangle=(a^b)==(c^d)
        previous_partition=previous_rectangle and (a&b)==(c&d)
        if not previous_partition:
            collisions.append({'a':a,'b':b,'c':c,'d':d,'previous_rectangle':previous_rectangle,
                               'previous_partition':previous_partition,'current_rows':[rows[x][1] for x in [a,b,c,d]]})
            if len(collisions)>=10:break
    else:seen[key]=(a,b)
out={'width':width,'future_steps_checked':steps,'pairs_checked':pair_count,
     'counterexample_candidates':collisions,'Lean_verified':False,'all_time_equality_proved':False,
     'full_problem_solved':False,'finite_only':True}
(ROOT/'backward-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
