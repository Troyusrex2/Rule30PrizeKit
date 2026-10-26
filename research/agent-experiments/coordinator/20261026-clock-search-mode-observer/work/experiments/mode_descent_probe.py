"""Test a clock-halving derivative observer on actual canonical plateau rows.
Membership failures refer only to the bounded-clock prefix graph. They do
not rule out a profile with higher-clock ancestors and subsequent drops.
"""
from pathlib import Path
import json,time,random
from profile_data import C,integral
r=Path(__file__).resolve().parent;START=time.monotonic();reports=[];witnesses=[]

def states_graph(P):
    states=[(0,0,0)];index={states[0]:0};parents=[None]
    for at,(u,v,d) in enumerate(states):
        drive=u|v
        if drive.bit_count()%2==0:
            for b in range(2):
                nxt=(v,integral(drive,b,P),C[d][b])
                if nxt not in index:index[nxt]=len(states);states.append(nxt);parents.append((at,b))
        assert len(states)<1500000
    def word(i):
        w=[]
        while parents[i] is not None:i,b=parents[i];w.append(b)
        return w[::-1]
    return states,word

def rotate(x,t,P):
    t%=P;mask=(1<<P)-1
    return ((x>>t)|(x<<(P-t)))&mask

def audit(d):
    P=d['clock'];w=d['initial_parent'];field=w.copy();h=[];k=[];l=[];g=[]
    q=0
    for b in w+[0]:q=C[q][b]
    assert q in {0,1,2,3,5}
    for t in range(2*P):
        g.append(field[-1]);h.append(field[-2]);k.append(field[-3] if len(field)>=3 else 0)
        l.append(field[-4] if len(field)>=4 else 0)
        nxt=[];a=b=0
        for x in field:nxt.append((30>>(4*x+2*a+b))&1);b,a=a,x
        field=nxt
    assert field==w
    H=sum(x<<t for t,x in enumerate(h));G=sum(x<<t for t,x in enumerate(g))
    obs=G|H;mask=(1<<P)-1;mode=(G^(G>>P))&mask
    rho=(obs^(obs>>P))&mask;S=mask^(rho^rotate(rho,1,P))
    assert mode==d['mode'] and S==d['derived_observation'] and rho==d['rho']
    assert all(h[t+P]==1-h[t] for t in range(P))
    assert all(k[t+P]==k[t] for t in range(P))
    assert all(mode>>t&1 ^ (mode>>((t+1)%P)&1)==1-k[t] for t in range(P))

audits=0
for P in [1,2,4,8,16,32,64]:
    states,word=states_graph(P);mask=(1<<P)-1
    profiles={v for u,v,d in states};pairs={(u,v) for u,v,d in states}
    groups=[{}, {}, {}];collisions=[None,None,None];samples=[];qmissing=pairmissing=0
    erosion_bad=golden_bad=mask_bad=0;first_erosion_failure=None;full_mode_collisions=0
    for index,(l,k,d) in enumerate(states):
        drive=l|k
        if drive.bit_count()%2==0:continue
        repeated=drive|(drive<<P);K=k|(k<<P)
        for b in [0,1]:
            H=integral(repeated,b,2*P);gdrive=H|K
            if gdrive.bit_count()%2:continue # this is a clock double, not a plateau
            for g0 in [0,1]:
                if C[C[C[d][b]][g0]][0] not in {0,1,2,3,5}:continue
                G=integral(gdrive,g0,2*P);q=(G^(G>>P))&mask;R=G|H;rho=(R^(R>>P))&mask
                S=mask^(rho^rotate(rho,1,P));v=(~k&~l)&mask
                assert S==(q|v)
                assert (q^rotate(q,1,P))==(mask^k)
                sample={'clock':P,'initial_parent':word(index)+[b,g0],'mode':q,
                        'derived_observation':S,'rho':rho,'original_OR':R,'newer_profile':G,
                        'older_profile':H,'original_older_pair':[l,k]}
                samples.append(sample);qmissing+=q not in profiles;pairmissing+=(v,q) not in pairs
                if S in groups[0] and groups[0][S]['mode']!=q:full_mode_collisions+=1
                if q!=(S&rotate(S,P-1,P)):
                    erosion_bad+=1
                    if first_erosion_failure is None:first_erosion_failure=sample
                golden_bad+=bool(q & rotate(q,2,P) & (~rotate(q,1,P)&mask))
                mask_bad+=bool((~q&~k&l)&mask)
                keys=[S,(S,rho&1),(S,rho&1,R&1)]
                for typ,key in enumerate(keys):
                    if key in groups[typ] and ((groups[typ][key]['mode']^q)&1) and collisions[typ] is None:
                        a=groups[typ][key];audit(a);audit(sample);audits+=2
                        collisions[typ]={'kind':['S_only','S_and_rho0','S_rho0_r0'][typ],
                                         'left':a,'right':sample,'mode_initial_bits_differ':True}
                        witnesses.append(collisions[typ])
                    else:groups[typ][key]=sample
    for d in random.Random(P).sample(samples,min(20,len(samples))):audit(d);audits+=1
    if first_erosion_failure is not None:audit(first_erosion_failure);audits+=1
    rec={'clock':P,'prefix_product_states':len(states),'canonical_plateau_rows':len(samples),
         'unique_derived_observations':len(groups[0]),'unique_modes':len({d['mode'] for d in samples}),
         'full_mode_collisions':full_mode_collisions,
         'mode_missing_from_same_clock_profile_graph':qmissing,'mode_pair_missing_from_same_clock_pair_graph':pairmissing,
         'derived_observer_collisions':[x['kind'] for x in collisions if x is not None],
         'quadratic_erosion_failures':erosion_bad,'mode_101_failures':golden_bad,
         'mode_mask_image_failures':mask_bad,'first_erosion_failure':first_erosion_failure}
    reports.append(rec);print(json.dumps(rec),flush=True)
out={'reports':reports,'collision_witnesses':witnesses,'literal_audits':audits,
     'same_clock_nonmembership_is_not_general_nonrealizability':True,'Lean_verified':False,
     'original_OR_observer_refuted':False,'full_problem_solved':False,'seconds':round(time.monotonic()-START,3)}
(r/'mode-descent-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='collision_witnesses'}),flush=True)
