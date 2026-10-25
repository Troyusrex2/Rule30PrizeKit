"""Bounded CNF falsification of total-spatial charge, using only no adjacent zeros.

Finite UNSAT is not a Lean proof. SAT witnesses are checked by direct
physical Rule 30 evolution of the reconstructed spatial row.
"""
import argparse,time
from core import save
from coupled_charge_cnf import Circuit,solve,pysat
from joint_spatial_charge import physical

def build(n,guard=True,prefixes=True,fixed=None):
    c=Circuit();free=[c.fresh() for _ in range(n)]
    if guard:
        for j in range(n-1):c.clauses.append(free[j:j+2])
    if fixed is not None:
        c.clauses.extend([[v if fixed>>i&1 else -v] for i,v in enumerate(free)])
    rows=[[-1]*(2*n+1),[1 if t%2==0 else free[t//2] for t in range(2*n)]]
    for d in range(2,2*n+1):
        rows.append([c.xor(rows[d-1][t+1],c.lor(rows[d-1][t],rows[d-2][t])) for t in range(2*n-d+1)])
    spatial=[rows[d+1][0] for d in range(2*n)];counter=[1]+[-1]*n;violations=[]
    for d in range(n):
        for lit in [free[d],spatial[2*d],spatial[2*d+1]]:
            counter=[1]+[c.lor(counter[j],-c.lor(-counter[j-1],-lit)) for j in range(1,n+1)]
        violations.append(-counter[d+1])
    c.clauses.append(violations if prefixes else violations[-1:])
    return c,free,spatial

def validate(n,f,s,m,guard,prefixes):
    free=[int(v in m) for v in f];spatial=sum(int(v in m)<<i for i,v in enumerate(s))
    physical(spatial,free)
    if guard:assert all(free[i:i+2]!=[0,0] for i in range(n))
    bad=[k for k in range(1,n+1) if (spatial&((1<<(2*k))-1)).bit_count()<free[:k].count(0)]
    assert bad if prefixes else n in bad
    return {'spatial_prefix_hex':hex(spatial),'free_prefix_hex':hex(sum(v<<i for i,v in enumerate(free))),
            'violating_prefixes':bad,'physical_evolution_recheck':True}

def main():
    p=argparse.ArgumentParser();p.add_argument('--length',type=int,default=48);p.add_argument('--seconds',type=float,default=90)
    p.add_argument('--solver',default='g4');a=p.parse_args();start=time.monotonic()
    for n,g,fix,expected in [(6,False,0x12,True),(5,True,None,False)]:
        c,f,s=build(n,g,fixed=fix);r,m,_=solve(c,a.solver,5);assert r is expected
        if r:validate(n,f,s,m,g,True)
    c,f,s=build(a.length);r,m,stats=solve(c,a.solver,a.seconds)
    out={'length':a.length,'guard':'no adjacent free zeros only','all_prefixes_checked':True,'factor':1,
         'actual_right_dynamics_enforced':False,'spatial_coordinates':'both odd and even, depths 1 through 2*n',
         'variables':c.nv,'clauses':len(c.clauses),'solver':a.solver,'pysat_version':pysat.__version__,
         'solver_status':'sat' if r else 'unsat' if r is False else 'unknown_timeout','solver_stats':stats,
         'controls':{'unrestricted_known_counterexample':True,'short_exhaustive_bound':True,'all_passed':True},
         'Lean_verified':False,'uniform_bound_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
    if r:out.update(validate(a.length,f,s,m,True,True))
    save(f'joint-spatial-charge-cnf-{a.length}-{a.solver}.json',out);print(out,flush=True)
if __name__=='__main__':main()
