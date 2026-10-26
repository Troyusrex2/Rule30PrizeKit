"""Independent scalar semantics and finite certificate corruption controls."""
from pathlib import Path
import copy,itertools,json
ROOT=Path(__file__).resolve().parent
d=json.loads((ROOT/'learned-reader.json').read_bytes())['dfa']
certificate=json.loads((ROOT/'invariance-product.json').read_bytes())
def run(word):
    q=d['start']
    for s in word:q=d['transitions'][q][s]
    return q in d['accepting']
def certificate_check(obj):
    states=[tuple(s) for s in obj['states']];allowed=set(states)
    assert (0,0,0,0) in allowed and len(allowed)==len(states)
    for a,b,p,q in states:
        assert (a in d['accepting'])==(b in d['accepting'])
        assert a not in d['accepting'] or p in [0,3]
        for s in range(4):
            # Truth-table definition, independent of packed numeric generator.
            aa=bool(s&2) ^ (bool(p&2) or bool(q&2))
            bb=bool(s&1) ^ (bool(p&1) or bool(q&1))
            out=2*int(aa)+int(bb)
            assert (d['transitions'][a][s],d['transitions'][b][out],s,p) in allowed
certificate_check(certificate)
rejected=[]
bad=copy.deepcopy(certificate);bad['states'][0][0]=15
try:certificate_check(bad)
except AssertionError:rejected.append('wrong_initial_classification')
bad=copy.deepcopy(certificate);bad['states'].pop()
try:certificate_check(bad)
except AssertionError:rejected.append('missing_reachable_state')
assert len(rejected)==2
tested=0;positive=0
for n in range(7):
    for word in itertools.product(range(4),repeat=n):
        a=sum(int(bool(s&2))<<j for j,s in enumerate(word));b=sum(int(bool(s&1))<<j for j,s in enumerate(word))
        same=True
        for t in range(1<<max(0,n-1)):
            if n:same &= ((a>>(n-1))&1)==((b>>(n-1))&1)
            a=a^((a<<1)|(a<<2));b=b^((b<<1)|(b<<2))
        assert run(word)==same;tested+=1;positive+=same
product=json.loads((ROOT/'clock-product.json').read_bytes())['reports']
assert [(r['temporal_clock'],r['closed']) for r in product]==[(2,True),(4,True),(8,True),(16,True)]
column=json.loads((ROOT/'column-graph.json').read_bytes())['reports']
assert column[-1]['clock']==64 and not column[-1]['closed']
assert all(r['nonconstant_OR_collision_pairs']==0 for r in column)
out={'passed':True,'scalar_membership_tests':tested,'positive_words':positive,'certificate_states':len(certificate['states']),
     'corruptions_rejected':rejected,'clock64_is_incomplete':True,
     'finite_tests_only':True,'Lean_verified':False,'reader_completeness_proved':False}
(ROOT/'independent-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
