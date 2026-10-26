"""Require actual h/g integration as well as local q/k/l equations.

The two oldest strip inputs remain unconstrained by finite white ancestry.
"""
from pathlib import Path
import json,time
from profile_data import integral
from mode_data import rotate
r=Path(__file__).resolve().parent;start=time.monotonic();reports=[]
for R in [2,4,8]:
    P=2*R;mask=(1<<P)-1;small=(1<<R)-1
    chosen={};rows=0;collision=None
    for K in range(1<<R):
        k=K|((small^K)<<R);dk=k^rotate(k,1,P)
        for L in range(1<<R):
            if L.bit_count()%2==0:continue
            l=L|(L<<R);dl=l^rotate(l,1,P)
            if l&~dk:continue
            m=dk&~l&mask
            if m&~dl:continue
            n=dl&~m&mask
            for h0 in [0,1]:
                H=integral((k|l)|((k|l)<<P),h0,2*P)
                assert ((H^(H>>P))&mask)==mask
                K2=k|(k<<P);Gdrive=H|K2
                assert Gdrive.bit_count()%2==0
                G=integral(Gdrive,0,2*P);q=(G^(G>>P))&mask
                S=q|(~k&~l&mask);rows+=1
                assert rotate(q,1,P)^q==mask^k
                assert dk==(l|m) and dl==(m|n)
                item={'R':R,'clock':P,'q':q,'k':k,'l':l,'m':m,'n':n,'S':S,'h':H,'g':G}
                if S in chosen and chosen[S]['q']!=q and collision is None:collision=[chosen[S],item]
                chosen.setdefault(S,item)
    out={'R':R,'clock':P,'admissible_local_rows':rows,'observations':len(chosen),'collision':collision}
    reports.append(out);print(json.dumps(out),flush=True)
out={'reports':reports,'all_cyclic_local_k_l_rows_at_listed_clocks':True,
     'genuine_plateau_q_from_h_g':True,'finite_white_ancestry_not_established':True,
     'Lean_verified':False,'uniform_mode_observer_proved':False,
     'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
(r/'mode-genuine-local-inverse.json').write_text(json.dumps(out,indent=2)+'\n')
