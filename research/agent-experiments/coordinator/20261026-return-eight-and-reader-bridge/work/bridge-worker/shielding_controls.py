"""Literal, independent audit of two all-time free-boundary controls."""
import json,re
from pathlib import Path
root=Path(__file__).parent
rule=(0,1,1,1,1,0,0,0)
def bits(n,P):return [n>>t&1 for t in range(P)]
def update_ok(r,p,x):
    P=len(x)
    return all(x[(t+1)%P]==rule[4*x[t]+2*p[t]+r[t]] for t in range(P))
def safe(x):return all(x[t] or x[(t+1)%len(x)] for t in range(len(x)))
# Spatially periodic ancestry: each profile is a complete period-eight word.
cycle=[202,178,172,43]
cy=[bits(n,8) for n in cycle]
assert all(update_ok(cy[(j-2)%4],cy[(j-1)%4],cy[j]) for j in range(4))
tail=[53,42,42];extended=cy+[bits(n,8) for n in tail]
assert all(update_ok(extended[j-2],extended[j-1],extended[j]) for j in range(4,7))
assert all(not safe(x) for x in extended)
assert (43|53)==(53|42)==63
assert extended[-3]!=extended[-2] and extended[-2]==extended[-1]
infinite={'cycle_oldest_to_newest':cycle,'tail':tail,'common_child':42,
          'different_parents':[53,42],'common_or':63,'all_ancestor_profiles_unsafe':True,
          'finite_white_ancestry':False,'literal_cycle_and_tail_audit':True}
# The prior four-column plateau strip, with the common child appended.
aa=['10101010','10011001','01101001','01010111']
bb=['11001100','01010101','01001011','00110101']
old=[]
for side in [aa,bb]:
    p=[list(map(int,s))*2 for s in side]
    r=[u|v for u,v in zip(p[-2],p[-1])]
    f=[0]
    for t in range(15):f.append(f[-1]^r[t])
    p.append(f)
    assert all(update_ok(p[j-2],p[j-1],p[j]) for j in range(2,5))
    old.append(p)
assert old[0][-1]==old[1][-1] and old[0][-2]!=old[1][-2]
assert not safe(old[0][-1]) and safe(old[1][1])
raw=(root/'CedarSafetySoundness.lean').read_text(encoding='utf-8')
states=[tuple(map(int,x)) for x in re.findall(r'\| (\d+) => ⟨(\d+), ofNat (\d+), ofNat (\d+)⟩',raw)]
allowed={q for i,q,p,r in states if q in [1,2,3,4,5,12]}
parents=sorted({r for i,q,p,r in states if q in allowed and p in [170,341]})
assert parents==[170,341,511] and 307 not in parents
report={'passed':True,'infinite_unsafe_ancestry_counterexample':infinite,
        'old_strip_common_child':''.join(map(str,old[0][-1])),
        'old_strip_B_alternating_k':bb[1],'old_strip_B_older_l':bb[0],
        'allowed_predecessor_profiles_of_accepted_alternating_column':parents,
        'scope':'Scalar cyclic audit only. No finite-white counterexample or Lean theorem asserted.'}
(root/'shielding-controls-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
