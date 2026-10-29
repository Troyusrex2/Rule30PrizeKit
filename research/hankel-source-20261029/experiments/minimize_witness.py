from pathlib import Path
import json,time
from pivot_probe import simulate
ROOT=Path(__file__).resolve().parent
def det(a):
    n=len(a);a=[r.copy() for r in a];sign=1;old=1
    for k in range(n-1):
        q=next((i for i in range(k,n) if a[i][k]),None)
        if q is None:return 0
        if q!=k:a[k],a[q]=a[q],a[k];sign=-sign
        p=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                x=a[i][j]*p-a[i][k]*a[k][j];assert x%old==0;a[i][j]=x//old
        for i in range(k+1,n):a[i][k]=0
        old=p
    return sign*a[-1][-1]
start=time.monotonic();K=134;rows=simulate(130,K);c=[(r>>K)&1 for r in rows];first=None
for t in range(1,129):
    if time.monotonic()-start>10:raise TimeoutError('fixed certificate minimization cap')
    fresh=((rows[t]>>K)&1)*((rows[t]>>(K+1))&1)
    if not fresh:continue
    for n in range(1,min(4,(t+1)//2)+1):
        s=t-2*n+1;parent=[[c[s+i+j] for j in range(n)] for i in range(n)]
        dp=det(parent)
        if dp%2==0:continue
        child=[[c[s+i+j] for j in range(n+1)] for i in range(n+1)]
        dc=det(child)
        if not dc:
            first={'offset':s,'size':n,'source_time':t,'fresh_source':fresh,'parent_determinant':dp,
              'child_determinant':dc,'parent':parent,'child':child,'center_prefix':c[:t+2],
              'source_right_neighbor':(rows[t]>>(K+1))&1}
            break
    if first:break
out={'status':'smaller_witness_found' if first else 'none_in_fixed_range','witness':first,'seconds':time.monotonic()-start}
(ROOT/'minimal-shifted-witness.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
