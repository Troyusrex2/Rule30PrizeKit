from pathlib import Path
import json,time
from backward_fields import Canonical,mode_space,kernel,image_of_kernel,contains
root=Path(__file__).resolve().parent
started=time.monotonic();history=Canonical(63);records=[]
for U in range(2,21):
    for V in range(1,U):
        positions=[p for p in range(-U,U+1) if history.bit(U,p)^history.bit(V,p)]
        prevpos=list(range(-U+1,U))
        current,cws=mode_space(history,U,V,U,positions)
        previous,pws=mode_space(history,U-1,V-1,U+1,prevpos)
        step=previous[1]
        white=[step.get(p,0) for p in range(-U,U+1) if p not in positions]
        sub=[1<<i for i,p in enumerate(prevpos) if not(history.bit(U-1,p)^history.bit(V-1,p))]
        full,_=image_of_kernel(white,len(prevpos),step,positions)
        dimensions=[];fullcover=[];restrictedcover=[]
        first_full=first_restricted=first_one=None
        first_bad_two=None
        for N in range(U+1):
            rows=[r for ws in cws[:N+1] for r in ws]
            prows=[r for ws in pws[:N+2] for r in ws]
            basis=kernel(rows,len(positions))
            restricted,_=image_of_kernel(white+sub+prows,len(prevpos),step,positions)
            cover=all(contains(full,v) for v in basis)
            rc=all(contains(restricted,v) for v in basis)
            dimensions.append(len(basis));fullcover.append(cover);restrictedcover.append(rc)
            if cover and first_full is None:first_full=N
            if rc and first_restricted is None:first_restricted=N
            if len(basis)==1 and first_one is None:first_one=N
            if N==2 and not cover:
                witness=next(v for v in basis if not contains(full,v))
                first_bad_two=[p for i,p in enumerate(positions) if witness>>i&1]
        assert first_one is not None
        assert dimensions==sorted(dimensions,reverse=True)
        assert fullcover==sorted(fullcover) and restrictedcover==sorted(restrictedcover)
        records.append({'U':U,'V':V,'dimensions':dimensions,'first_all_finite_lift':first_full,
                        'first_subset_common_lift':first_restricted,'first_dimension_one':first_one,
                        'N2_nonliftable_mode':first_bad_two})
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,'records':records,
     'max_first_finite_lift':max(records,key=lambda r:r['first_all_finite_lift']),
     'max_first_restricted_lift':max(records,key=lambda r:r['first_subset_common_lift']),
     'max_first_one_dimension':max(records,key=lambda r:r['first_dimension_one']),
     'first_N2_nonliftable':next((r for r in records if r['N2_nonliftable_mode']),None),
     'seconds':time.monotonic()-started}
(root/'lift-delays.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='records'}))
