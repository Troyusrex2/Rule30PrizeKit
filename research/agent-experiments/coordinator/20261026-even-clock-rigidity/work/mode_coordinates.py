"""Test representation and quadratic-inversion hypotheses for admissible modes."""
from pathlib import Path
import json,time,random
import numpy as np
from mode_data import states_graph,rotate,audit,C,integral
r=Path(__file__).resolve().parent;START=time.monotonic();reports=[];negative=None

def data_for(P):
    states,word=states_graph(P);mask=(1<<P)-1;chosen={}
    byprofile={};bypair={}
    for i,(l,k,d) in enumerate(states):byprofile.setdefault(k,i);bypair.setdefault((l,k),i)
    for i,(l,k,d) in enumerate(states):
        drive=l|k
        if drive.bit_count()%2==0:continue
        for b in [0,1]:
            H=integral(drive|(drive<<P),b,2*P);K=k|(k<<P);gdrive=H|K
            if gdrive.bit_count()%2:continue
            for g0 in [0,1]:
                if C[C[C[d][b]][g0]][0] not in {0,1,2,3,5}:continue
                G=integral(gdrive,g0,2*P);q=(G^(G>>P))&mask;R=G|H;rho=(R^(R>>P))&mask
                S=mask^(rho^rotate(rho,1,P));assert S==q|((~k&~l)&mask)
                if S in chosen:assert chosen[S]['mode']==q
                else:chosen[S]={'clock':P,'initial_parent':word(i)+[b,g0],'mode':q,
                    'derived_observation':S,'rho':rho,'original_OR':R,
                    'newer_profile':G,'older_profile':H,'original_older_pair':[l,k]}
    return list(chosen.values()),states,word,byprofile,bypair

def span_quadratic(samples,P):
    M=len(samples);values=np.array([x['derived_observation'] for x in samples],dtype=np.uint64)
    packed=np.packbits(((values[None,:]>>np.arange(P,dtype=np.uint64)[:,None])&1).astype(np.uint8),axis=1,bitorder='little')
    obs=[int.from_bytes(row.tobytes(),'little') for row in packed]
    bits=np.packbits(np.array([x['mode']&1 for x in samples],dtype=np.uint8),bitorder='little')
    target=int.from_bytes(bits.tobytes(),'little');basis={};terms=[];ranks=[];answer=None
    for degree in range(3):
        candidates=[((),(1<<M)-1)] if degree==0 else ([( (i,),obs[i]) for i in range(P)] if degree==1 else
             [( (i,j),obs[i]&obs[j]) for i in range(P) for j in range(i+1,P)])
        for term,v in candidates:
            e=1<<len(terms);terms.append(term)
            while v:
                p=v.bit_length()-1
                if p not in basis:basis[p]=(v,e);break
                b,be=basis[p];v^=b;e^=be
        residual=target;expression=0
        while residual and residual.bit_length()-1 in basis:
            b,be=basis[residual.bit_length()-1];residual^=b;expression^=be
        ranks.append({'degree':degree,'rank':len(basis),'target_recovered':residual==0})
        if not residual:
            answer=[list(term) for i,term in enumerate(terms) if (expression>>i)&1];break
    witness=None
    if residual:
        dual=1<<(residual.bit_length()-1)
        for p,(v,e) in sorted(basis.items()):
            if (v&dual).bit_count()%2:dual^=1<<p
        assert dual.bit_count()%2==0 and (target&dual).bit_count()%2==1
        assert all((f&dual).bit_count()%2==0 for f in obs)
        assert all((obs[i]&obs[j]&dual).bit_count()%2==0 for i in range(P) for j in range(i+1,P))
        selected=[x for i,x in enumerate(samples) if (dual>>i)&1]
        witness={'clock':P,'rows':selected,'size':len(selected),'all_monomials_degree_le_two_zero':True,'target_xor':1}
    if answer is not None:
        for x in samples:
            value=0
            for term in answer:
                v=1
                for t in term:v&=(x['derived_observation']>>t)&1
                value^=v
            assert value==(x['mode']&1)
    return ranks,answer,witness

for P in [4,16,32,64]:
    t=time.monotonic();samples,states,word,profiles,pairs=data_for(P);mask=(1<<P)-1
    drives={l|k:i for i,(l,k,d) in enumerate(states)}
    checks={key:0 for key in ['S_actual_profile','rho_actual_profile','S_actual_OR','notS_actual_OR']}
    representations=[];first_missing={}
    for sample in samples:
        S=sample['derived_observation'];rho=sample['rho']
        for key,value,space in [('S_actual_profile',S,profiles),('rho_actual_profile',rho,profiles),
                                ('S_actual_OR',S,drives),('notS_actual_OR',mask^S,drives)]:
            if value in space:
                checks[key]+=1
                if len(representations)<12:
                    representations.append({'kind':key,'source_parent':sample['initial_parent'],
                                            'representative':word(space[value]),'clock':P})
            elif key not in first_missing:first_missing[key]=sample
    ranks,terms,witness=span_quadratic(samples,P)
    for x in random.Random(P).sample(samples,min(16,len(samples))):audit(x)
    for x in first_missing.values():audit(x)
    if witness:
        for x in witness['rows']:audit(x)
        (r/f'mode-quadratic-negative-P{P}.json').write_text(json.dumps(witness,indent=2)+'\n')
    out={'clock':P,'mode_classes':len(samples),'bounded_clock_membership_counts':checks,
         'membership_failures_are_not_general_nonrealizability':True,'first_missing':first_missing,
         'representative_examples':representations,'quadratic_layers':ranks,'filter_terms':terms,
         'quadratic_negative_size':witness['size'] if witness else None,'seconds':round(time.monotonic()-t,3)}
    reports.append(out);print(json.dumps({k:v for k,v in out.items() if k not in ['first_missing','representative_examples','filter_terms']}),flush=True)
    (r/'mode-coordinate-probe.json').write_text(json.dumps({'reports':reports,'Lean_verified':False,
         'uniform_observer_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-START,3)},indent=2)+'\n')
