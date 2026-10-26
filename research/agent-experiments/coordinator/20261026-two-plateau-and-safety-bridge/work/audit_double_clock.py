from pathlib import Path
import json
root=Path(__file__).resolve().parent
data=json.loads((root/'double-clock-safe-probe.json').read_bytes());results=[]
for r in data['results']:
    if r['status']!='sat':continue
    values=r['profiles'];R=r['R'];T=r['clock'];white_failures=0
    def bit(j,t):return (values[j]>>(t%T))&1
    for t in range(T):
        for j in range(2,6):assert bit(j,t+1)==(bit(j,t)^(bit(j-1,t)|bit(j-2,t)))
        assert bit(2,t+R)==bit(2,t)
        assert bit(3,t+R)==1-bit(3,t)
        assert bit(4,t+2*R)==1-bit(4,t)
        assert bit(5,t) or bit(5,t+1)
        if r['oldest_profiles_R_periodic']:
            for j in [0,1]:assert bit(j,t+R)==bit(j,t)
        white_failures+=(bit(0,t+1)!=bit(0,t))
        white_failures+=(bit(1,t+1)!=(bit(1,t)^bit(0,t)))
    results.append({'R':R,'clock':T,'older_R':r['oldest_profiles_R_periodic'],
        'all_literal_and_clock_constraints_passed':True,'genuine_white_equation_failures':white_failures})
# Exact positive finite-white control for R=2, not just arbitrary old inputs.
row=[1,0,0,0,0,1];start=list(row);history=[]
for _ in range(8):
    history.append(row)
    row=[row[j] ^ ((row[j-1] if j>=1 else 0)|(row[j-2] if j>=2 else 0)) for j in range(6)]
assert row==start
assert all(history[t][-1] or history[(t+1)%8][-1] for t in range(8))
assert all(history[(t+2)%8][3]==1-history[t][3] and history[(t+4)%8][4]==1-history[t][4] for t in range(8))
(root/'double-clock-independent-audit.json').write_text(json.dumps({'results':results,
    'finite_white_R2_control':[1,0,0,0,0,1],'finite_white_R2_control_passed':True,
    'no_genuine_white_counterexample_claim':True},indent=2)+'\n',encoding='utf-8')
print('Eight relaxed models independently audited; genuine finite-white R2 control passes.')
