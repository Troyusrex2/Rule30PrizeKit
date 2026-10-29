from pathlib import Path
import json,time,importlib.util
P=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('pivot',P/'pivot_probe.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)

def det(a):
    a=[list(r) for r in a];n=len(a);sign=1;old=1
    if n==0:return 1
    for k in range(n-1):
        pivot=next((i for i in range(k,n) if a[i][k]),None)
        if pivot is None:return 0
        if pivot!=k:a[k],a[pivot]=a[pivot],a[k];sign=-sign
        p=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                x=a[i][j]*p-a[i][k]*a[k][j]
                assert x%old==0
                a[i][j]=x//old
        for i in range(k+1,n):a[i][k]=0
        old=p
    return sign*a[-1][-1]

start=time.monotonic();K=70;states=m.simulate(64,K);c=[(r>>K)&1 for r in states]
ds={n:det([[c[i+j] for j in range(n)] for i in range(n)]) for n in range(1,34)}
records=[];bad=[]
for n in range(1,33):
    assert time.monotonic()-start<30
    if not ds[n]%2:continue
    fresh=((states[2*n-1]>>K)&1)&((states[2*n-1]>>(K+1))&1)
    if not fresh:continue
    r={'n':n,'det_parent':ds[n],'det_child':ds[n+1],'child_mod2':ds[n+1]%2}
    records.append(r)
    if not ds[n+1]:bad.append(r)
result={'status':'candidate_refuted' if bad else 'not_refuted_in_fixed_range',
        'candidate_cases':records,'counterexamples':bad,
        'zero_leading_determinants':[n for n,d in ds.items() if d==0],
        'n2_integer_border_pivot':{'numerator':ds[3],'denominator':ds[2]},
        'seconds':time.monotonic()-start,'scope':'Finite exact Python only, not a proof of any infinite rank statement'}
(P/'integer-lift-result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
