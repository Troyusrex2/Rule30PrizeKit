"""Test a cubic decoder of the lower mode, distinct from the raw-head test."""
from pathlib import Path
import itertools,json,random,time
import numpy as np
from gf2_block import eliminate,pivot,dual_vector,features
from mode_samples import data_for
r=Path(__file__).resolve().parent;start=time.monotonic();reports=[]
def pack(values):
    b=np.packbits(np.array(values,dtype=np.uint8),bitorder='little')
    return np.pad(b,(0,(-len(b))%8)).view(np.uint64)
def reduced(v,basis):
    while v:
        p=v.bit_length()-1
        if p not in basis:return v
        v^=basis[p]
    return 0
for P in [4,16,32,64]:
    t=time.monotonic();samples,states,word,_,_=data_for(P);M=len(samples)
    values=[x['derived_observation'] for x in samples]
    obs=np.array([pack([(x>>i)&1 for x in values]) for i in range(P)])
    target=pack([x['mode']&1 for x in samples]);original=target.copy()
    matrix=features(obs,M)
    print(json.dumps({'clock':P,'mode_classes':M,'matrix_bytes':matrix.nbytes,'stage':'eliminating'}),flush=True)
    rank,pivots=eliminate(matrix,target);residual=pivot(target)
    report={'clock':P,'mode_classes':M,'cubic_rank':int(rank),'target_recovered':residual<0,
            'seconds':round(time.monotonic()-t,3)}
    if P<=32:
        scalar={};scalar_obs=[int.from_bytes(row.tobytes(),'little') for row in obs]
        for deg in range(4):
            for term in itertools.combinations(range(P),deg):
                v=(1<<M)-1
                for i in term:v&=scalar_obs[i]
                v=reduced(v,scalar)
                if v:scalar[v.bit_length()-1]=v
        assert len(scalar)==rank
        assert (not reduced(int.from_bytes(original.tobytes(),'little'),scalar))==(residual<0)
        report['independent_python_rank_check']=True
    if residual>=0:
        dual=dual_vector(matrix,pivots,residual);di=int.from_bytes(dual.tobytes(),'little')
        assert di.bit_count()%2==0
        obsint=[int.from_bytes(row.tobytes(),'little') for row in obs]
        assert (di&int.from_bytes(original.tobytes(),'little')).bit_count()%2==1
        checked=0
        for deg in range(4):
            for term in itertools.combinations(range(P),deg):
                v=di
                for i in term:v&=obsint[i]
                assert v.bit_count()%2==0;checked+=1
        chosen=[x for i,x in enumerate(samples) if di>>i&1]
        # Packed scalar Rule 30 evolution on every selected literal prefix.
        for x in chosen:
            bits=x['initial_parent'];width=len(bits);w=sum(b<<j for j,b in enumerate(bits));initial=w
            g=[];h=[]
            state=0
            for b in bits+[0]:state=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]][state][b]
            assert state in [0,1,2,3,5]
            for tick in range(2*P):
                g.append(w>>(width-1)&1);h.append(w>>(width-2)&1)
                w=(w^((w<<1)|(w<<2)))&((1<<width)-1)
            assert w==initial
            q=[g[t+P]^g[t] for t in range(P)]
            rho=[(g[t+P]|h[t+P])^(g[t]|h[t]) for t in range(P)]
            S=[1^rho[t]^rho[(t+1)%P] for t in range(P)]
            assert sum(b<<t for t,b in enumerate(q))==x['mode']
            assert sum(b<<t for t,b in enumerate(S))==x['derived_observation']
        witness={'clock':P,'rows':chosen,'row_count':len(chosen),'moments_independently_checked':checked,
                 'all_degree_le_three_moments_zero':True,'target_xor':1,
                 'all_selected_prefix_cycles_packed_scalar_checked':True,'Lean_verified':False}
        (r/f'mode-cubic-negative-P{P}.json').write_text(json.dumps(witness,indent=2)+'\n')
        report['negative_witness_rows']=len(chosen);report['monomials_checked']=checked
    reports.append(report);print(json.dumps(report),flush=True)
    (r/'mode-cubic-probe.json').write_text(json.dumps({'reports':reports,
        'all_prefix_ancestors_P_periodic':True,'Lean_verified':False,
        'uniform_mode_observer_refuted':False,'full_problem_solved':False,
        'seconds':round(time.monotonic()-start,3)},indent=2)+'\n')
