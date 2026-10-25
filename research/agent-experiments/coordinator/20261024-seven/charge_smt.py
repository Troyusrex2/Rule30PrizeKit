"""Bounded symbolic search for charge counterexamples; solver results are not proofs."""
import argparse,json,sys,time
from core import BASE,HERE,save
sys.path.insert(0,str(BASE/'toolchain/python-research'))
import z3
from coupled_even_code_probe import even_code,decode,forbidden,packed_run

def model(n,factor,timeout_ms,fixed=None):
    solver=z3.Solver();solver.set(timeout=timeout_ms,max_memory=1536)
    free=[z3.Bool(f's_{i}') for i in range(n)]
    if fixed is not None:
        for s,v in zip(free,fixed):solver.add(s==bool(v))
    for i in range(n-1):solver.add(z3.Or(free[i],free[i+1]))
    for i in range(n-4):solver.add(z3.Or(*[z3.Not(s) for s in free[i:i+5]]))
    rows=[[z3.BoolVal(False)]*(2*n+1),[z3.BoolVal(True) if t%2==0 else free[t//2] for t in range(2*n)]]
    for d in range(2,2*n+1):
        row=[]
        for t in range(2*n-d+1):
            v=z3.Bool(f'r_{d}_{t}')
            solver.add(v==z3.Xor(rows[d-1][t+1],z3.Or(rows[d-1][t],rows[d-2][t])))
            row.append(v)
        rows.append(row)
    evens=[rows[2*d+2][0] for d in range(n)]
    solver.add(z3.PbGe([(z3.Not(s),1) for s in free]+[(e,-factor) for e in evens],1))
    return solver,free,evens,rows

def controls():
    cases=[(2,1,None,z3.unsat),(3,1,[0,1,0],z3.sat),
           (11,2,[0,1,0,1,0,1,1,0,1,1,0],z3.sat)]
    for n,c,fixed,expected in cases:
        solver,free,evens,_=model(n,c,5000,fixed);assert solver.check()==expected
        if expected==z3.sat:
            m=solver.model();s=[int(z3.is_true(m.eval(b))) for b in free]
            u=sum(int(z3.is_true(m.eval(e)))<<i for i,e in enumerate(evens))
            assert even_code(s)==u and decode(u,n)==s and c*u.bit_count()<s.count(0)
    return {'bounded_control_cases':len(cases),'all_passed':True}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--length',type=int,default=64)
    parser.add_argument('--factor',type=int,default=8);parser.add_argument('--timeout-ms',type=int,default=45000)
    args=parser.parse_args();checked=controls();start=time.monotonic()
    solver,free,evens,rows=model(args.length,args.factor,args.timeout_ms);status=solver.check()
    out={'length':args.length,'factor':args.factor,'solver':z3.get_version_string(),
         'solver_verdict':str(status),'timeout_ms':args.timeout_ms,'controls':checked,
         'Lean_verified':False,'unbounded_charge_proved':False,'full_problem_solved':False}
    if status==z3.sat:
        m=solver.model();s=[int(z3.is_true(m.eval(b))) for b in free]
        u=sum(int(z3.is_true(m.eval(e)))<<i for i,e in enumerate(evens))
        packed=sum(int(z3.is_true(m.eval(rows[d][0])))<<(d-1) for d in range(1,2*args.length+1))
        assert forbidden(s) is None and even_code(s)==u and decode(u,args.length)==s
        assert args.factor*u.bit_count()<s.count(0)
        x=packed
        for t in range(2*args.length):
            assert x&1==(1 if t%2==0 else s[t//2]);x=(x>>1)^(x|(x<<1))
        out.update({'free_prefix':s,'finite_even_input':u,'packed_initial_row':packed,
                    'even_black_count':u.bit_count(),'free_zeros':s.count(0),
                    'independent_scalar_and_physical_checks':True})
    elif status==z3.unknown:out['reason_unknown']=solver.reason_unknown()
    out['seconds']=round(time.monotonic()-start,3);save(f'charge-smt-{args.length}-factor{args.factor}.json',out)
    print({k:v for k,v in out.items() if k!='free_prefix'},flush=True)

if __name__=='__main__':main()
