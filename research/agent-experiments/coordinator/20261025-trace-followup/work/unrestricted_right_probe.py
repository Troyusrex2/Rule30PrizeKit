"""Different fixed left edges, right initial cells unconstrained through the cone.

SAT supplies only a finite matching prefix. UNSAT is diagnostic, not a Lean
premise or all-edges theorem. This is not the old fixed-width edge-bound test.
"""
from pathlib import Path
import json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root.parent.parent/'z3-deps'))
import z3

def signature(a,c,n):
    s=0
    for t in range(n):
        s|=((a>>(c+t))&1)<<t
        a ^= (a<<1)|(a<<2)
    return s

def probe(m,n,H,timeout=20000):
    assert H>m>n>0
    c=H;width=c+H
    a=z3.BitVec(f'a_{m}_{n}_{H}',c+m+1)
    b=z3.BitVec(f'b_{m}_{n}_{H}',c+n+1)
    solver=z3.SolverFor('QF_BV')
    solver.set(timeout=timeout,max_memory=1536)
    solver.add(z3.Extract(c+m,c+m,a)==1,z3.Extract(c+n,c+n,b)==1)
    x=z3.ZeroExt(width-a.size(),a);y=z3.ZeroExt(width-b.size(),b)
    for t in range(H):
        solver.add(z3.Extract(c+t,c+t,x)==z3.Extract(c+t,c+t,y))
        x ^= (x<<1)|(x<<2);y ^= (y<<1)|(y<<2)
    started=time.monotonic();verdict=solver.check()
    result={'edge_depths':[m,n],'observations':H,'right_cells_unconstrained_through':c,
            'verdict':str(verdict),'solver':z3.get_version_string(),
            'seconds':time.monotonic()-started,'Lean_verified':False}
    if verdict==z3.sat:
        model=solver.model();av=model.eval(a).as_long();bv=model.eval(b).as_long()
        assert av.bit_length()==c+m+1 and bv.bit_length()==c+n+1
        assert signature(av,c,H)==signature(bv,c,H)
        d=signature(av,c,4*H)^signature(bv,c,4*H)
        result.update(initial_rows_hex=[hex(av),hex(bv)],center_index=c,
                      first_difference_with_zero_tail=(d&-d).bit_length()-1 if d else None)
    if verdict==z3.unknown:result['reason_unknown']=solver.reason_unknown()
    print(json.dumps(result),flush=True)
    return result

controls=[probe(2,1,8),probe(2,1,9)]
assert [r['verdict'] for r in controls]==['sat','unsat']
test=probe(5,4,32)
result={'controls':controls,'probe':test,'finite_observation_only':True,
        'unbounded_edge_observability_proved':False,'full_problem_solved':False}
(root/'unrestricted-right-probe.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
