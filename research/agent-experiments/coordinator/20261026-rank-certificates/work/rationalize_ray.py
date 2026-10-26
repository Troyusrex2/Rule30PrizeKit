"""Reconstruct Farkas weights by exact sparse integer elimination.
Only a nonnegative exact null vector with positive RHS counts as a proof
of infeasibility of the recorded finite linear system. No solver is trusted.
"""
from pathlib import Path
from fractions import Fraction
from collections import defaultdict
from functools import reduce
import json,math,time
root=Path(__file__).resolve().parent;reports=[]
def canonical(d):
    d={j:v for j,v in d.items() if v}
    if not d:return d
    g=reduce(math.gcd,(abs(v) for v in d.values()))
    if d[min(d)]<0:g=-g
    return {j:v//g for j,v in d.items()}
def reconstruct(raw):
    maximum=max(abs(v) for v in raw['dual_ray'])
    support=[i for i,v in enumerate(raw['dual_ray']) if v>maximum*1e-10]
    eqs=[{} for _ in range(raw['variables'])]
    for j,i in enumerate(support):
        for col,c in raw['rows'][i].items():eqs[int(col)][j]=c
    piv={};start=time.monotonic()
    for row in eqs:
        row=canonical(row)
        while row:
            if time.monotonic()-start>90:return {'status':'elimination_time_cap'}
            p=min(row)
            if p not in piv:piv[p]=row;break
            old=piv[p];a=row[p];b=old[p]
            new={j:b*v for j,v in row.items()}
            for j,v in old.items():new[j]=new.get(j,0)-a*v
            row=canonical(new)
    free=sorted(set(range(len(support)))-piv.keys())
    rec={'support':len(support),'rank':len(piv),'nullity':len(free)}
    if not free:return dict(rec,status='no_null_vector_on_selected_support')
    # Preserve approximate free coordinates; then solve all pivot equations exactly.
    for denominator in [10,1000,1000000,1000000000]:
        y={j:Fraction(raw['dual_ray'][support[j]]/maximum).limit_denominator(denominator) for j in free}
        for p,row in sorted(piv.items(),reverse=True):
            y[p]=-sum((c*y[j] for j,c in row.items() if j!=p),Fraction())/row[p]
        if any(v<0 for v in y.values()):continue
        margin=sum((y[j]*raw['rhs'][i] for j,i in enumerate(support)),Fraction())
        sums=defaultdict(Fraction)
        for j,i in enumerate(support):
            for col,c in raw['rows'][i].items():sums[int(col)]+=y[j]*c
        if margin>0 and all(v==0 for v in sums.values()):
            weights=[[i,str(y[j])] for j,i in enumerate(support) if y[j]]
            return dict(rec,status='exact_farkas',margin=str(margin),weights=weights)
    return dict(rec,status='reconstructed_vectors_not_nonnegative')
for K,moment in [(2,True),(3,False),(3,True)]:
    start=time.monotonic();name=f'lp-raw-{K}-{int(moment)}.json'
    raw=json.loads((root/name).read_bytes());rec=reconstruct(raw)
    rec.update(context=K,first_moment=moment,seconds=round(time.monotonic()-start,3))
    if rec['status']=='exact_farkas':
        cert={'weights':rec.pop('weights'),'rhs_margin':rec['margin'],'system_file':name}
        cname=f'farkas-exact-{K}-{int(moment)}.json'
        (root/cname).write_text(json.dumps(cert,indent=2)+'\n',encoding='utf-8');rec['certificate_file']=cname
    reports.append(rec);print(json.dumps(rec),flush=True)
    (root/'rationalized-rays.json').write_text(json.dumps({'reports':reports,'Lean_verified':False,
        'sink_separation_proved':False,'full_problem_solved':False},indent=2)+'\n',encoding='utf-8')
