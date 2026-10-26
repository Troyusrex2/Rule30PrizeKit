"""Test one proposed invariant on saved genuine orbits, not a width census."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
src=root/'inputs/height_controls.json'
raw=src.read_bytes();records=json.loads(raw);checks=[];counter=[]
def step(row):
    return [v ^ ((row[j-1] if j else 0)|(row[j-2] if j>=2 else 0)) for j,v in enumerate(row)]
for rec in records:
    rows=[list(map(int,w)) for w in rec['orbit']];P=len(rows)
    assert rows[0]==list(map(int,rec['word']))
    assert all(step(rows[t])==rows[(t+1)%P] for t in range(P))
    for j in range(len(rows[0])):
        col=[r[j] for r in rows];p=P
        while p>1 and p%2==0 and col[:p//2]==col[p//2:p]:p//=2
        if p<16:continue
        trace=col[:p];height=[0]
        for t,x in enumerate(trace):height.append(height[-1]+(-1 if t%2 else 1)*(1-x))
        span=max(height)-min(height);drift=height[-1]
        item={'seed_word':rec['word'],'column':j,'effective_prefix':rec['word'][:j+1],'least_trace_period':p,'white_height_span':span,'white_height_drift':drift}
        checks.append(item)
        if drift==0 and span<=2:
            counter.append(dict(item,trace=trace,height=height))
result={'input_sha256':hashlib.sha256(raw).hexdigest(),'saved_orbits_checked':len(records),'genuine_column_checks':checks,'counterexamples':counter,'candidate':'Every genuine finite-white column of least period>=16 has nonzero white-height drift OR span>2.','candidate_refuted':bool(counter),'candidate_proved':False,'kernel_verified':False,'scope':'Independent literal replay and exact periods of saved named orbits only; no expanded search.'}
(root/'result.json').write_bytes((json.dumps(result,indent=2)+'\n').encode())
print(json.dumps({'saved_orbits':len(records),'high_period_columns':len(checks),'counterexamples':len(counter),'first_counterexample':counter[0] if counter else None,'candidate_proved':False}))
