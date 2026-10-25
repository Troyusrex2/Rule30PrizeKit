"""Exact finite-band common-mode search in canonical moving right frames.

All tested bands and phases are finite. A surviving mode is only called
all-time after checking a complete returning background/field matrix cycle.
"""
from pathlib import Path
import json,time
from backward_fields import echelon,kernel
root=Path(__file__).resolve().parent;started=time.monotonic()
def orbit(L):
    mask=(1<<(L+1))-1;x=1;rows=[]
    while not rows or x!=1:
        rows.append(x);x=(x^((x<<1)|(x<<2)))&mask
        assert len(rows)<=1<<L
    return rows
def add_row(pivots,row):
    while row:
        p=row.bit_length()-1
        if p not in pivots:pivots[p]=row;break
        row^=pivots[p]
summaries=[];survivors=[];global_max=0;scalar_controls=0
for L in range(1,14):
    rows=orbit(L);T=len(rows);cases=0;latest_kill=0;worst=None
    period=T*(1<<(L-1).bit_length())
    # P=L+1 represents every larger age gap: B is identically white on
    # all coefficient/readout cells used by this band, and all A phases occur.
    for P in range(1,L+2):
        for V in range(T):
            A=rows[(V+P)%T];B=(rows[V]<<P)&((1<<(L+1))-1);delta=A^B
            positions=[j for j in range(L) if delta>>j&1];n=len(positions)
            field=[0]*L
            for i,j in enumerate(positions):field[j]=1<<i
            initial=tuple(field);pivots={};killed=None
            for t in range(period):
                A=rows[(V+P+t)%T];B=(rows[(V+t)%T]<<P)&((1<<(L+1))-1);delta=A^B
                for j in range(1,L+1):
                    row=((field[j-1] if delta>>j&1 else 0) ^
                         (field[j] if j<L and delta>>(j-1)&1 else 0))
                    add_row(pivots,row)
                field2=[]
                for j in range(L+2):
                    row=(field[j] if j<L else 0) ^ \
                        (field[j-1] if 0<=j-1<L and not(B>>(j-2)&1 if j>=2 else 0) else 0) ^ \
                        (field[j-2] if 0<=j-2<L and not(A>>(j-1)&1) else 0)
                    field2.append(row)
                for row in field2[L:]:add_row(pivots,row)
                if len(pivots)==n:killed=t;break
                field=field2[:L]
            if killed is None:
                assert tuple(field)==initial,(L,P,V,T,'field matrix did not return')
                modes=kernel(list(pivots.values()),n)
                assert modes
                survivors.append({'L':L,'P':P,'V_phase':V,'background_period':T,
                                  'checked_return_period':period,'initial_positions':positions,
                                  'mode_vectors':modes})
            elif killed>latest_kill:
                latest_kill=killed;worst={'P':P,'V_phase':V,'initial_variables':n}
            cases+=1
    summaries.append({'L':L,'background_period':T,'cases':cases,'latest_kill_step':latest_kill,'worst':worst})
    print(json.dumps(summaries[-1]),flush=True)
out={'finite_band_scope_only':True,'Lean_verified':False,'full_problem_solved':False,
     'all_age_gaps_covered_at_each_tested_width':True,
     'widths':summaries,'cycle_verified_survivors':survivors,'seconds':time.monotonic()-started}
(root/'escaping-band-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'survivors':len(survivors),'seconds':out['seconds']}))
