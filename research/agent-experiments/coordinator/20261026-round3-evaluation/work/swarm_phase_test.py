"""Falsify the literal four-step interface and test phase-bucket agreement."""
from pathlib import Path
import json,statistics
ROOT=Path(__file__).resolve().parent
T=60000;K=128;row=1;rows=[];center=[]
for t in range(T):
    rows.append(row);center.append(row>>t&1);row^=(row<<1)|(row<<2)
def depth(t,p):
    a,b=rows[t],rows[t-p]<<(2*p)
    return a.bit_length()-(a^b).bit_length() if a!=b else a.bit_length()
d=[None]*100+[depth(t,16) for t in range(100,T)]
literal_bad=[t for t in range(100,T-4) if d[t+4]!=d[t]+3]
assert literal_bad
slopes={}
for end in [12000,30000,60000]:
    ts=range(100,end)
    slopes[str(end)]=sum(t*d[t] for t in ts)/sum(t*t for t in ts)
phase=[]
for k in range(1,K+1):
 for q in range(4):
    indices=range(100+((q-100)%4),T-k,4)
    n=len(indices);matches=sum(center[t]==center[t+k] for t in indices)
    phase.append({'lag':k,'initial_phase':q,'terminal_phase':(q+k)%4,'samples':n,'agreement':matches/n})
assert all(.46<r['agreement']<.54 for r in phase)
t=literal_bad[0]
report={'finite_only':True,'Lean_verified':False,'T':T,'lags':K,
        'literal_four_step_law':False,'four_step_violations':len(literal_bad),
        'first_violation':{'t':t,'depth_t':d[t],'depth_t_plus_four':d[t+4],'predicted':d[t]+3},
        'slope_through_origin_by_endpoint':slopes,
        'phase_buckets':phase,'phase_agreement_range':[min(r['agreement'] for r in phase),max(r['agreement'] for r in phase)],
        'geometry':'If the interface is at -t/4 and the center at 0, their distance is t/4, not 5t/4.',
        'asymptotic_slope_proved_or_disproved':False,'full_problem_solved':False}
(ROOT/'swarm-phase-test.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='phase_buckets'}),flush=True)
