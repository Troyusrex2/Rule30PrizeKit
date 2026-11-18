"""Verify the stated witnesses from the literal Rule 30 truth table, without importing the search."""
import json

CASES = [
    (2483979780129110, (10,10,10,10,6,6), (6,)),
    (2440786724530854946624415088918, (6,10,10,10,10,6,10,10,6,6,10,6), (6,10)),
    (348215574720768951329435505750294, (6,6,10,10,6,10,6,10,6,6,10,6,10,6), (6,6)),
]

def literal_step(row):
    # Increasing j goes toward the physical LEFT, away from the fixed white wall.
    return {j for j in range(max(row)+2)
            if (30 >> (4*(j+1 in row) + 2*(j in row) + (j-1 in row))) & 1}

def diagonal(rows,t):
    return {j for j in range(t+1) if j in rows[t-j]}

def measurements(rows,t):
    a,b = diagonal(rows,t), diagonal(rows,t-1)
    end = max(a|b)+1
    return dict(t=t, width=end, mass=[len(a),len(b)], R=2*len(a)+len(b),
                histogram=[sum(2*(j in a)+(j in b)==v for j in range(end)) for v in range(4)])

def physical_width_from_pair(rows,t):
    surface = [2*j for j in diagonal(rows,t)]
    surface.extend(2*j+1 for j in diagonal(rows,t-1))
    return 1+max(surface)

results=[]
for seed,before,group in CASES:
    t0=sum(before)
    assert seed.bit_length()<=t0+1
    rows=[{i for i in range(seed.bit_length()) if (seed >> i)&1}]
    for _ in range(t0+sum(group)):
        rows.append(literal_step(rows[-1]))
    trace=''.join('1' if 0 in row else '0' for row in rows)
    assert trace=='0'+''.join('1'*(d-1)+'0' for d in before+group)
    snapshots=[measurements(rows,t0)]
    for d in group:
        snapshots.append(measurements(rows,snapshots[-1]['t']+d))
    for t in range(t0,len(rows)-1):
        a,b,c=diagonal(rows,t),diagonal(rows,t-1),diagonal(rows,t+1)
        assert physical_width_from_pair(rows,t)==1+max(rows[t])
        overlap=len(a & {j+1 for j in b})
        adjacent=sum(j+1 in c for j in c)
        assert 2*len(c)-len(a)-len(b)==2*adjacent+(0 in c)-overlap
    h0,h1=snapshots[0]['histogram'],snapshots[-1]['histogram']
    results.append(dict(seed=str(seed), seed_width=seed.bit_length(),group=group,states=snapshots,
                        delta=[b-a for a,b in zip(h0,h1)]))
assert [p['R'] for p in results[0]['states']]==[80,93]
assert results[1]['delta']==[-1,6,6,-3] and results[2]['delta']==[7,-5,-2,6]
assert all(x+y>0 for x,y in zip(results[1]['delta'],results[2]['delta']))
print(json.dumps(results,indent=2))

switch_seed=CASES[1][0]
switch_rows=[{i for i in range(switch_seed.bit_length()) if (switch_seed>>i)&1}]
for _ in range(125):
    switch_rows.append(literal_step(switch_rows[-1]))
def rhythm_pair(t):
    return tuple(next(k for k in range(len(switch_rows)-t)
                      if (0 in switch_rows[t+k])!=(k%d!=0)) for d in (6,10))
assert rhythm_pair(100)==(12,6) and rhythm_pair(106)==(6,12)

# Exhaust finite small seeds to detect orientation and off-by-one errors in the
# paper argument. These checks supplement the proof for arbitrary widths.
width_checks = 0
agreement_checks = 0
for seed in range(1,64):
    rows=[{i for i in range(seed.bit_length()) if (seed>>i)&1}]
    for _ in range(60):
        rows.append(literal_step(rows[-1]))
    for t in range(seed.bit_length()-1,seed.bit_length()+4):
        width=physical_width_from_pair(rows,t)
        assert width==1+max(rows[t])==seed.bit_length()+t
        width_checks+=1
        for d in (6,10):
            diff=rows[t]^rows[t+d]
            first=min(diff)
            mismatch=next(k for k in range(width+d)
                          if (0 in rows[t+k]) != (0 in rows[t+d+k]))
            assert mismatch==first
            end=next(k for k in range(width+2*d)
                     if (0 in rows[t+k]) != (k%d!=0))
            assert end<=d+first<=width+2*d-1
            agreement_checks+=1
print('PASS',width_checks,'width identities and',agreement_checks,'rhythm bounds')
