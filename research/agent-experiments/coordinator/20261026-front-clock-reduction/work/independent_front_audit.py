"""Scalar controls for temporal-prefix and source-cut calculations."""
from pathlib import Path
import itertools,json
ROOT=Path(__file__).resolve().parent
def advance(a):
    return [a[j] ^ ((a[j-1] if j>=1 else 0) | (a[j-2] if j>=2 else 0)) for j in range(len(a))]
def mode(a,b,h):
    return [h[j] ^ ((1^(b[j-2] if j>=2 else 0)) & (h[j-1] if j>=1 else 0)) ^
            ((1^(a[j-1] if j>=1 else 0)) & (h[j-2] if j>=2 else 0)) for j in range(len(h))]
def common(a,b,h):
    d=[x^y for x,y in zip(a,b)]
    return all((d[j]*h[j+1])==(h[j]*d[j+1]) for j in range(len(d)-1))
# Independently check all eight possible next-column initial triples for a
# representative nonconstant first-source clock. No finite time detection:
# length-five prefix has the already-proved period bound16.
extension=[]
for ai,bi,hi in itertools.product(range(2),repeat=3):
    a=[1,0,0,0,ai];b=[0,1,0,1,bi];h=[0,0,0,1,hi]
    first=None;initial=(a[:],b[:],h[:])
    for t in range(16):
        if not common(a,b,h) and first is None:first=t
        a,b,h=advance(a),advance(b),mode(a,b,h)
    assert (a,b,h)==initial
    assert first is not None
    extension.append({'new_initial':[ai,bi,hi],'first_common_failure':first})
# Check every possible period-two input clock and initial f,x state.
accepted=0;tested=0
for q0,d0,d1,f0,x0 in itertools.product(range(2),repeat=5):
    q=[q0^(t%2) for t in range(9)];d=[(d0,d1)[t%2] for t in range(9)]
    f=[f0];x=[x0]
    for t in range(8):
        f.append(f[-1]^((1^q[t])*d[t]));x.append(x[-1]^(1^q[t]))
    z=[v*w for v,w in zip(f,x)]
    if all(z[t+1]==(z[t]^((1^q[t])*f[t])) for t in range(8)):
        assert all(v==f0 for v in f);accepted+=1
    tested+=1
# Exact cut decomposition control on a protected-prefix finite pair.
def packed_m(a):return a^((a<<1)|(a<<2))
def packed_d(a,b,h):return h^((~(b<<2))&(h<<1))^((~(a<<1))&(h<<2))
a,b,h=2,11,1;wrong_cut_rejected=False
for t in range(64):
    delta=a^b;next_delta=packed_m(a)^packed_m(b)
    cut=delta&~7
    assert packed_d(a,b,cut)==(next_delta&~7)
    assert h==(delta^cut)
    bad=delta&~1
    if packed_d(a,b,bad)!=(next_delta&~1):wrong_cut_rejected=True
    a,b,h=packed_m(a),packed_m(b),packed_d(a,b,h)
assert wrong_cut_rejected
result=json.loads((ROOT/'temporal-front-14.json').read_bytes())
assert result['controls']==2730
assert all(not r['surviving_example'] and not r['nonalternating_neighbor_disagreements'] for r in result['records'])
assert all(set(r['front_and_shared_clock_periods']).issubset({'(4, 2)'}) for r in result['records'])
assert all(not r['uncovered_clock_cases'] for r in result['records'])
assert sum(r['varying_front_candidates'] for r in result['records'])==2288
out={'passed':True,'all_next_column_triples_rejected':extension,'clock_cases':tested,'accepted_clock_cases_constant':accepted,
     'cut_decomposition_times':64,'wrong_cut_rejected':wrong_cut_rejected,
     'clock_premises_cover_all_2288_tested_front_candidates':True,
     'finite_only':True,'Lean_verified':False,'unbounded_collision_classification_proved':False}
(ROOT/'independent-front-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
