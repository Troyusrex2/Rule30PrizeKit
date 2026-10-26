"""Falsify a proposed local mode inverse before using global ancestry."""
from pathlib import Path
import json,time
from profile_data import integral
from mode_data import rotate
r=Path(__file__).resolve().parent;start=time.monotonic();reports=[]
for R in [1,2,4,8]:
    P=2*R if R%2==0 else 4*R;mask=(1<<P)-1;small=(1<<R)-1
    chosen={};rows=0;collision=None
    for K in range(1<<R):
        k=K|((small^K)<<R)
        if P==4*R:k|=k<<(2*R)
        dk=k^rotate(k,1,P)
        for L in range(1<<R):
            l=sum(L<<i for i in range(0,P,R));dl=l^rotate(l,1,P)
            if l&~dk:continue
            m=dk&~l&mask
            if m&~dl:continue
            n=dl&~m&mask
            for bit in [0,1]:
                q=integral(mask^k,bit,P);S=q|(~k&~l&mask);rows+=1
                assert rotate(q,1,P)^q==mask^k
                assert dk==(l|m) and dl==(m|n)
                item={'R':R,'clock':P,'q':q,'k':k,'l':l,'m':m,'n':n,'S':S}
                if S in chosen and (chosen[S]['q']&1)!=(q&1) and collision is None:
                    collision=[chosen[S],item]
                chosen.setdefault(S,item)
    out={'R':R,'clock':P,'admissible_local_rows':rows,'observations':len(chosen),'collision':collision}
    reports.append(out);print(json.dumps(out),flush=True)
result={'reports':reports,'all_cyclic_local_rows_at_listed_clocks':True,
        'finite_white_ancestry_not_established':True,'h_antiperiod_not_supplied':True,
        'Lean_verified':False,'uniform_mode_observer_proved':False,
        'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
(r/'mode-local-inverse.json').write_text(json.dumps(result,indent=2)+'\n')
