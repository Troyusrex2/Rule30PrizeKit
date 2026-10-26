"""Check whether the clock lemma needs periodicity of the older mask l."""
from pathlib import Path
import json,time
from profile_data import integral
from mode_data import rotate
r=Path(__file__).resolve().parent;start=time.monotonic();reports=[]
for R in [1,2,4]:
    P=2*R if R%2==0 else 4*R;mask=(1<<P)-1;small=(1<<R)-1
    rows=0;counter=None
    for K in range(1<<R):
        k=K|((small^K)<<R)
        if P==4*R:k|=k<<(2*R)
        dk=k^rotate(k,1,P)
        for l in range(1<<P):
            dl=l^rotate(l,1,P)
            if l&~dk:continue
            m=dk&~l&mask
            if m&~dl:continue
            n=dl&~m&mask
            for q0 in [0,1]:
                q=integral(mask^k,q0,P);S=q|(~k&~l&mask);rows+=1
                assert rotate(q,1,P)^q==mask^k and dk==(l|m) and dl==(m|n)
                if rotate(S,R,P)==S and counter is None:
                    counter={'q':q,'k':k,'l':l,'m':m,'n':n,'S':S}
    report={'R':R,'clock':P,'local_rows':rows,'counterexample':counter}
    reports.append(report);print(json.dumps(report),flush=True)
out={'reports':reports,'older_mask_period_premise_not_used':True,'Lean_verified':False,
     'uniform_proof_not_inferred_from_finite_search':True,'full_problem_solved':False,
     'seconds':round(time.monotonic()-start,3)}
(r/'mode-unrestricted-mask-probe.json').write_text(json.dumps(out,indent=2)+'\n')
