"""Measure complete escape delays from the no-00 safety condition."""
from pathlib import Path
import json,time
import numpy as np
from numba import njit
r=Path(__file__).resolve().parent;start=time.monotonic()
@njit(cache=False)
def canonical(n,w):
    if n==0:return True
    p=0
    while not (n>>p)&1:p+=1
    d=w-p
    return d<=2 or (d>=4 and ((n>>(p+1))&1)==((n>>(p+2))&1))
@njit(cache=False)
def audit(w):
    size=1<<w;mask=size-1;seen=np.zeros(size,np.uint8)
    maximum=0;seed=0;cm=0;cs=0
    for init in range(size):
        if seen[init]:continue
        v=init;run=0;leading=0;bad=False;local=0;local_seed=0;runstart=init
        while True:
            assert not seen[v];seen[v]=1
            if v>>(w-3):
                if run==0:runstart=v
                run+=1
                if run>local:local=run;local_seed=runstart
            else:
                if not bad:leading=run
                bad=True;run=0
            v=(v^((v<<1)|(v<<2)))&mask
            if v==init:break
        if not bad:continue
        if leading+run>local:local=leading+run;local_seed=runstart
        if local>maximum:maximum=local;seed=local_seed
        if canonical(init,w) and local>cm:cm=local;cs=local_seed
    return maximum,seed,cm,cs
reports=[]
for w in [6,8,10,12,14,16,18,20,22,24,26]:
    t=time.monotonic();m,s,cm,cs=audit(w)
    # Independent literal Rule 30 audit of the maximizing witnesses.
    for steps,initial in [(m,s),(cm,cs)]:
        row=[initial>>j&1 for j in range(w)]
        for tick in range(steps+1):
            assert (any(row[-3:]))==(tick<steps)
            row=[row[0],row[1]^row[0]]+[(30>>(4*row[j]+2*row[j-1]+row[j-2]))&1 for j in range(2,w)]
    out={'width':w,'all_words':1<<w,'max_finite_safe_run':int(m),'maximizer':int(s),
         'max_canonical_safe_run':int(cm),'canonical_maximizer':int(cs),
         'seconds':round(time.monotonic()-t,3)}
    reports.append(out);print(json.dumps(out),flush=True)
    (r/'safe-delay-profile.json').write_text(json.dumps({'reports':reports,'finite_widths_only':True,
        'complete_orbits_no_time_cap':True,'maximizers_literal_checked':True,
        'Lean_verified':False,'uniform_escape_bound_proved':False,'full_problem_solved':False,
        'seconds':round(time.monotonic()-start,3)},indent=2)+'\n')
