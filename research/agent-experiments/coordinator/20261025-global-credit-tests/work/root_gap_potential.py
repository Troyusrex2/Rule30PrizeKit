"""Test source-aware gap resources for the checked greedy least-root frontier.
Every candidate is an explicit unbounded nonnegative natural/ordinal resource,
not a score on all disagreement blocks. Failures are finite witnesses only.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib,json,random,time
import numpy as np
from scipy.optimize import linprog
root=Path(__file__).resolve().parent;started=time.monotonic()
def phi(a):return a^((a<<1)|(a<<2))
def low(a):return (a&-a).bit_length()-1
def runs(d):
    out=[]
    while d:
        lo=low(d);le=((d>>lo)^((d>>lo)+1)).bit_length()-1
        out.append((lo,le));d&=~(((1<<le)-1)<<lo)
    return out
def features(a,b,j,frame):
    mask=(a^b)>>j;rr=runs(mask);gaps=[rr[i+1][0]-rr[i][0]-rr[i][1] for i in range(len(rr)-1)]
    dist=j-frame;assert dist>0 and mask&1
    blocks=[le for _,le in rr]
    values=[dist,mask.bit_count(),len(rr),sum(gaps),sum(v*v for v in gaps),sum(v**3 for v in gaps),
            max(gaps,default=0),sum(v*v for v in blocks),max(blocks),
            gaps[0] if gaps else 0,gaps[1] if len(gaps)>1 else 0,len(gaps)]
    return values,gaps,blocks
names=['front_distance','root_population','root_blocks','total_gap','gap_square','gap_cube','maximum_gap',
       'block_square','maximum_block','front_gap','second_gap','gap_count']
cases=[(T,P) for T in [0,1,2,3,7,15,31,63,127,255] for P in [1,2,3,4,7,8,16,32]]
rng=random.Random(30302523)
cases += [(rng.randrange(256,2048),rng.randrange(1,129)) for _ in range(32)]
last=max(T+P+8*(T+P)+256 for T,P in cases)
rows=[1]
for _ in range(last+3):rows.append(phi(rows[-1]))
records=[];states=set();duplicates=0;hits=[]
ordinal={'gap_then_distance':{'failures':0,'first':None},'block_then_distance':{'failures':0,'first':None},
         'distance_then_gap':{'failures':0,'first':None}}
domination=None;mask_crosschecks=0
for T,P in cases:
    frame=T+P;j=2*frame;j0=j;full=1<<j;horizon=8*frame+256
    for t in range(horizon):
        n=T+t;f=frame+t;a=rows[n]<<P;b=rows[n+P]
        dist=j-f
        if dist<=0:hits.append({'T':T,'P':P,'time':t,'front':-dist});break
        j1=j+low(((rows[n+1]<<P)^rows[n+P+1])>>j)
        j2=j1+low(((rows[n+2]<<P)^rows[n+P+2])>>j1)
        if T+P<512:
            dn=(rows[n+1]<<P)^rows[n+P+1]
            fn=dn&(full|(full<<1)|(full<<2))
            assert low(fn)==j1 and fn==dn&~((1<<j1)-1)
            mask_crosschecks+=1
        key=(n,P,j)
        if key in states:duplicates+=1
        else:
            states.add(key)
            guard=all((rows[n+i]>>(n+i)&1)==(rows[n+P+i]>>(n+P+i)&1) for i in range(3))
            if guard and j2>f+2:
                before,g0,b0=features(a,b,j,f)
                after,g1,b1=features(rows[n+2]<<P,rows[n+P+2],j2,f+2)
                rec={'T':T,'P':P,'elapsed':t,'effective_onset':n,'root_index':j,'next_root_index':j2,
                     'before':before,'after':after,'before_gaps':g0,'after_gaps':g1,
                     'before_blocks':b0,'after_blocks':b1}
                records.append(rec)
                pairs={'gap_then_distance':((sorted(g0,reverse=True),before[0]),(sorted(g1,reverse=True),after[0])),
                       'block_then_distance':((sorted(b0,reverse=True),before[0]),(sorted(b1,reverse=True),after[0])),
                       'distance_then_gap':((before[0],sorted(g0,reverse=True)),(after[0],sorted(g1,reverse=True)))}
                for name,(old,new) in pairs.items():
                    if not new<old:
                        ordinal[name]['failures']+=1
                        if ordinal[name]['first'] is None:ordinal[name]['first']=rec
                if domination is None and all(y>=x for x,y in zip(before,after)):
                    domination=rec
        j=j1
        if T+P<512:full=fn
    else:hits.append({'T':T,'P':P,'unknown_after':horizon})
assert records
A=np.asarray([np.asarray(r['after'],dtype=float)-r['before'] for r in records])
lp=linprog(np.ones(len(names)),A_ub=A,b_ub=-np.ones(len(records)),bounds=(0,None),method='highs',options={'time_limit':30.})
out={'finite_only':True,'Lean_verified':False,'source_aware':True,'rng_seed':30302523,
     'case_count':len(cases),'guarded_distinct_root_transitions':len(records),'duplicate_root_states_skipped':duplicates,
     'deduplication':'effective onset n, lag P, and current root cut j; T+t alone does not identify a history-dependent root cut',
     'full_mask_crosschecks':mask_crosschecks,'feature_names':names,'ordinal_candidates':ordinal,
     'coordinatewise_nonnegative_potential_counterexample':domination,
     'nonnegative_linear_potential_lp':{'status':lp.status,'message':lp.message,'weights':lp.x.tolist() if lp.success else None},
     'first_hits_or_unknowns':hits,'seconds':time.monotonic()-started,
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'Three explicit source-aware ordinal resources and a nonnegative linear combination of the listed natural features. A componentwise counterexample refutes all coordinatewise-monotone functions of these features, but not signed potentials with separate lower-bound proofs, history-dependent hydra ranks, or arbitrary source-aware invariants.'}
(root/'root-gap-potential.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'cases':len(cases),'transitions':len(records),'ordinal_failures':{k:v['failures'] for k,v in ordinal.items()},
                  'componentwise_witness':domination,'LP_status':lp.status,'seconds':out['seconds']}),flush=True)
