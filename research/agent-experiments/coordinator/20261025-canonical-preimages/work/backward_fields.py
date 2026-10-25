"""Exact finite-horizon common-mode spaces and canonical backward images.

No finite horizon is asserted to characterize all-time compatibility.
"""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent

def echelon(rows):
    pivots={}
    for row in rows:
        while row:
            p=row.bit_length()-1
            if p not in pivots:pivots[p]=row;break
            row ^= pivots[p]
    return pivots

def contains(pivots,row):
    while row:
        p=row.bit_length()-1
        if p not in pivots:return False
        row ^= pivots[p]
    return True

def kernel(rows,n):
    pivots=echelon(rows);result=[]
    for free in range(n):
        if free in pivots:continue
        row=1<<free
        for p in sorted(pivots):
            if (pivots[p]&row).bit_count()%2:row ^= 1<<p
        assert all((r&row).bit_count()%2==0 for r in pivots.values())
        result.append(row)
    assert len(result)==n-len(pivots)
    return result

def F(a):return (a<<1)^(a|(a>>1))

class Canonical:
    def __init__(self,maximum):
        self.origin=maximum+4;self.rows=[1<<self.origin]
        for _ in range(maximum):self.rows.append(F(self.rows[-1]))
    def bit(self,t,p):return (self.rows[t]>>(self.origin+p))&1

def mode_space(history,U,V,H,positions):
    assert U>V>=0
    actual=sum((history.bit(U,p)^history.bit(V,p))<<i for i,p in enumerate(positions))
    field={p:1<<i for i,p in enumerate(positions)}
    wrows=[];fields=[]
    for t in range(H+1):
        fields.append(field)
        lo,hi=-U-t,U+t
        delta=lambda p:history.bit(U+t,p)^history.bit(V+t,p)
        assert all(((field.get(p,0)&actual).bit_count()%2)==delta(p) for p in range(lo,hi+1))
        ws=[]
        for p in range(lo-1,hi+1):
            row=(field.get(p,0) if delta(p+1) else 0) ^ (field.get(p+1,0) if delta(p) else 0)
            if row:ws.append(row)
        assert all((row&actual).bit_count()%2==0 for row in ws)
        wrows.append(ws)
        if t<H:
            field={p:(field.get(p-1,0) ^
                      (field.get(p,0) if not history.bit(V+t,p+1) else 0) ^
                      (field.get(p+1,0) if not history.bit(U+t,p) else 0))
                   for p in range(lo-1,hi+2)}
    return fields,wrows

def project(field,vector,positions):
    return sum(((field.get(p,0)&vector).bit_count()%2)<<i for i,p in enumerate(positions))

def image_of_kernel(rows,n,field,positions):
    basis=kernel(rows,n)
    images=[project(field,v,positions) for v in basis]
    pivots=echelon(images)
    assert len(pivots)==len(basis) # finite D preimages are unique
    return pivots,images

def analyze(history,U,V):
    horizons=sorted(set([0,1,U,2*U,4*U]));H=max(horizons)
    curpos=[p for p in range(-U,U+1) if history.bit(U,p)^history.bit(V,p)]
    prevpos=list(range(-U+1,U))
    curfields,curWs=mode_space(history,U,V,H,curpos)
    prevfields,prevWs=mode_space(history,U-1,V-1,H+1,prevpos)
    step=prevfields[1];prevn=len(prevpos)
    allcurrent=list(range(-U,U+1))
    columns=[project(step,1<<i,allcurrent) for i in range(prevn)]
    assert len(echelon(columns))==prevn
    cokernel=kernel(columns,len(allcurrent));assert len(cokernel)==2
    white=[step.get(p,0) for p in allcurrent if p not in curpos]
    subset=[1<<i for i,p in enumerate(prevpos) if not(history.bit(U-1,p)^history.bit(V-1,p))]
    full,_=image_of_kernel(white,prevn,step,curpos)
    subs,_=image_of_kernel(white+subset,prevn,step,curpos)
    results=[]
    for N in horizons:
        currows=[r for ws in curWs[:N+1] for r in ws]
        prevrows=[r for ws in prevWs[:N+2] for r in ws]
        basis=kernel(currows,len(curpos))
        common,common_vectors=image_of_kernel(white+prevrows,prevn,step,curpos)
        restricted,restricted_vectors=image_of_kernel(white+prevrows+subset,prevn,step,curpos)
        assert all(all((row&v).bit_count()%2==0 for row in currows) for v in common_vectors+restricted_vectors)
        record={'U':U,'V':V,'through':N,'current_dimension':len(basis),
                'all_finite_image_dimension':len(full),'subset_image_dimension':len(subs),
                'common_image_dimension':len(common),'subset_common_image_dimension':len(restricted)}
        for name,space in [('all_finite',full),('subset',subs),('common',common),('subset_common',restricted)]:
            witness=next((v for v in basis if not contains(space,v)),None)
            record[name+'_covers_current']=witness is None
            if witness is not None:
                pos=[p for i,p in enumerate(curpos) if witness>>i&1]
                data={'initial_h_positions':pos,'initial_delta_positions':curpos}
                if name=='all_finite':
                    whole=sum(1<<(p+U) for p in pos)
                    dual=next(q for q in cokernel if (q&whole).bit_count()%2)
                    assert all((q&col).bit_count()%2==0 for q in [dual] for col in columns)
                    data['finite_image_obstruction_positions']=[p for i,p in enumerate(allcurrent) if dual>>i&1]
                record[name+'_witness']=data
        results.append(record)
    return results

def main():
    started=time.monotonic();maximum=20;history=Canonical(5*maximum+3)
    records=[]
    for U in range(2,maximum+1):
        for V in range(1,U):records.extend(analyze(history,U,V))
    late=[r for r in records if r['through']==4*r['U']]
    out={'finite_horizon_only':True,'Lean_verified':False,'full_problem_solved':False,
         'maximum_U':maximum,'pairs':len(late),'records':records,
         'late_all_finite_failures':sum(not r['all_finite_covers_current'] for r in late),
         'late_subset_common_failures':sum(not r['subset_common_covers_current'] for r in late),
         'first_late_finite_failure':next((r for r in late if not r['all_finite_covers_current']),None),
         'first_late_restricted_failure':next((r for r in late if not r['subset_common_covers_current']),None),
         'seconds':time.monotonic()-started}
    (root/'backward-fields.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k!='records'}))

if __name__=='__main__':main()
