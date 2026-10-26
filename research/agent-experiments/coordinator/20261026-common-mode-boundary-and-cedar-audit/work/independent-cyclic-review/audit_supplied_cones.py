"""Independently evaluate supplied finite-cone witnesses; never invokes SAT."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
source=ROOT/'supplied/common-subset-cone-probe.json'
data=json.loads(source.read_bytes());results=[]
assert [r['horizon'] for r in data['reports']]==[1,2,3,4,6,8,12]
for case in data['reports']:
    h=case['horizon'];n=case['initial_width'];target=case['target']
    assert case['status']=='sat' and n==4*h+6 and target==2*h+2
    a,b,m=(case['rows'][label] for label in ['a','b','h'])
    assert all(len(rows)==h+1 and all(len(row)==n and all(x in (0,1) for x in row) for row in rows) for rows in [a,b,m])
    assert all((m[0][j] & (a[0][j]^b[0][j]))==m[0][j] for j in range(n))
    checks=dict(actual=0,mode=0,common=0)
    for t in range(h+1):
        for j in range(2*t,n-1):
            assert ((a[t][j]^b[t][j]) & m[t][j+1]) == (m[t][j] & (a[t][j+1]^b[t][j+1]))
            checks['common']+=1
        if t==h:continue
        for j in range(2*(t+1),n):
            for rows in [a,b]:
                literal=(30>>(4*rows[t][j]+2*rows[t][j-1]+rows[t][j-2]))&1
                boolean=rows[t][j] ^ (rows[t][j-1] | rows[t][j-2])
                assert rows[t+1][j]==literal==boolean
                checks['actual']+=1
            expected=m[t][j] ^ ((1-b[t][j-2]) & m[t][j-1]) ^ ((1-a[t][j-1]) & m[t][j-2])
            assert m[t+1][j]==expected
            checks['mode']+=1
    assert 2<=target<n and m[1][target]==1 and a[1][target]==b[1][target]
    results.append(dict(horizon=h,width=n,target=target,initial_subset=True,subset_loss_time=1,
        scalar_checks=checks,passed=True))
report=dict(passed=True,search_performed=False,kernel_checked=False,
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),reports=results,
    scope='Finite triangular domains only. At time t equations and Common are checked only at j>=2t. No equations constrain the excluded older boundary, and no all-time extension is established. These are different witnesses from the six-cycle transient and the verifier-created H12 white cone.')
(ROOT/'supplied-cones-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
