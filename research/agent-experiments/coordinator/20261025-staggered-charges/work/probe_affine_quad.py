from pathlib import Path
from itertools import combinations
import json
root=Path(__file__).resolve().parent

def step(a):return a ^ ((a<<1)|(a<<2))
survivors=[]
for q in combinations(range(16),4):
    if q[0]^q[1]^q[2]^q[3]:continue
    s=q;history=[]
    for t in range(129):
        if s[0]^s[1]^s[2]^s[3]:break
        if t<12:history.append(list(s))
        s=tuple(step(a) for a in s)
    else:
        survivors.append({'initial':q,'first_twelve':history})
assert len(survivors)==2
result={'survivors_through_128':survivors,'all_time_proved':False,'full_problem_solved':False}
(root/'affine-quad-probe.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
