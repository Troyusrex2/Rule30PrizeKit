"""Independent literal replay of saved strips; no SCC or ancestry claim."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
src=root/'free_strip_safety.json'
if not src.is_file():
    src=Path('D:/MWB/Rule30/agent-inbox/r30-codex-cedar-d3-20261026-2dc049fe-v03/artifacts/integration/free_strip_safety.json')
raw=src.read_bytes();data=json.loads(raw);width=data['width'];results=[]
assert width==10 and data['oldest_free_cells']==2
for name in ('bad_cycle','power_two_bad_cycle'):
    rec=data[name];states=rec['states_with_wrap'];assert states[0]==states[-1]
    rows=[[bool(s & (1<<j)) for j in range(width)] for s in states];p=len(rows)-1
    for row,nxt in zip(rows,rows[1:]):
        for j in range(2,width):assert nxt[j]==(row[j] != (row[j-1] or row[j-2]))
    trace=[r[-1] for r in rows[:-1]];assert trace==rec['newest_bits']
    assert all(trace[t] or trace[(t+1)%p] for t in range(p))
    assert any(trace[t]!=trace[(t+8)%p] for t in range(p))
    least=min(k for k in range(1,p+1) if all(trace[t]==trace[(t+k)%p] for t in range(p)))
    assert least==p
    assert all([trace[(t+j)%p] for j in range(5)] != [True,True,False,True,True] for t in range(p))
    violations=[(t,j) for t in range(p) for j in range(2) if rows[t+1][j] != (rows[t][j] != (rows[t][0] if j==1 else False))]
    assert violations
    results.append({'name':name,'least_newest_period':least,'checked_internal_updates':p*8,'safe_including_wrap':True,'non8':True,'avoids_11011':True,'white_boundary_failures':violations})
result={'passed':True,'input_sha256':hashlib.sha256(raw).hexdigest(),'audits':results,'kernel_verified':False,'finite_white_counterexample':False,'scope':'Saved cycles only; no graph/SCC construction rerun.'}
(root/'free_strip_safety.json').write_bytes(raw)
(root/'cycle-audit.json').write_bytes((json.dumps(result,indent=2)+'\n').encode())
print(json.dumps({'passed':True,'periods':[r['least_newest_period'] for r in results],'finite_white_counterexample':False}))
