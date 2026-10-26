"""Test a necessary physical right extension omitted by the sideways relaxation."""
from pathlib import Path
import itertools,json
ROOT=Path(__file__).resolve().parent

def left_check(u,v):
    right,center=list(v),list(u)
    for d in range(1,len(u)):
        width=min(len(center)-1,len(right))
        if width<=0:break
        left=[center[t+1]^(center[t]|right[t]) for t in range(width)]
        if any((t<d and value!=0) or (t==d and value!=1) for t,value in enumerate(left)):
            return False
        right,center=center,left
    return True

def right_check(u,v):
    return all(not v[t] or v[t+1]==(1^u[t]) for t in range(min(len(u),len(v)-1)))

truth_controls=0
for u,v,nxt in itertools.product(range(2),repeat=3):
    feasible=any(nxt==(u^(v|w)) for w in range(2))
    assert feasible==(not v or nxt==(1^u))
    truth_controls+=1
records=[]
for N in range(4,9):
    u=[1,1]+[0]*(N-2)
    old=[list(v) for v in itertools.product(range(2),repeat=N) if left_check(u,v)]
    new=[v for v in old if right_check(u,v)]
    records.append({'N':N,'left_only_survivors':len(old),'right_admissible_survivors':len(new),
                    'old_example':old[0] if old else None})
assert next(r['N'] for r in records if r['right_admissible_survivors']==0)==5

# Independent literal physical evolution with arbitrary finite right initial
# words, retaining a leftmost black cell at the origin.
controls=0
for right in range(64):
    row={0}|{p+1 for p in range(6) if right>>p&1}
    u=[];v=[]
    for t in range(32):
        u.append(int(0 in row));v.append(int(1 in row))
        row={p for p in range(min(row)-1,max(row)+2)
             if ((p-1 in row) ^ ((p in row) or (p+1 in row)))}
    for N in range(4,33):
        assert left_check(u[:N],v[:N]) and right_check(u[:N],v[:N])
        controls+=1

# Impose a periodic center, evolve its entire right half from white initial
# data, and reconstruct leftward. This actually satisfies the premise that
# the original unconditional real-orbit density measurement did not impose.
n=2048;u=[t%2 for t in range(n+2)]
row=0;v=[]
for t in range(n+2):
    v.append(row&1)
    row=(row<<1)^(row|(row>>1))^u[t]
left1=[u[t+1]^(u[t]|v[t]) for t in range(n+1)]
left2=[left1[t+1]^(left1[t]|u[t]) for t in range(n)]
P=2
e=[left1[t]^left1[t+P] for t in range(n-P)]
e2=[left2[t]^left2[t+P] for t in range(n-P-1)]
assert all(e2[t]==(e[t]^e[t+1]) for t in range(len(e2)))
lo,hi=128,2000
mass1=sum(e[lo:hi]);mass2=sum(e2[lo:hi])
assert mass2>mass1
report={'passed':True,'truth_table_controls':truth_controls,'physical_prefix_controls':controls,
        'constant_tail_yardstick':records,'first_unsat_width_with_right_admissibility':5,
        'periodic_center_conditional_control':{'period':P,'window':[lo,hi],
           'depth1_defect_count':mass1,'depth2_defect_count':mass2,
           'identity':'delta(-2,t)=delta(-1,t+1) XOR delta(-1,t)',
           'canonical_seed_or_left_finite_background':False},
        'finite_only':True,'Lean_verified':False,'full_problem_solved':False}
(ROOT/'right-admissibility.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
