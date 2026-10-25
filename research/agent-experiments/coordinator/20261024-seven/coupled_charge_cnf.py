"""Independent CNF encoding of the actual two-sided charge counterexample.

All gates and cardinality use Boolean CNF; no pseudo-Boolean Z3 arithmetic.
Finite UNSAT remains outside Lean. SAT models are checked by physical rules.
"""
import argparse,sys,threading,time
from core import BASE,save
sys.path.insert(0,str(BASE/'toolchain/sat-research'))
import pysat
from pysat.solvers import Solver
from pysat.card import CardEnc,EncType
from empty_right_absorption import step
from coupled_even_code_probe import decode,even_code,forbidden

class Circuit:
    def __init__(self):self.nv=1;self.clauses=[[1]]
    def fresh(self):self.nv+=1;return self.nv
    def lor(self,a,b):
        if 1 in [a,b] or a==-b:return 1
        if a==-1:return b
        if b==-1 or a==b:return a
        v=self.fresh();self.clauses += [[-a,v],[-b,v],[a,b,-v]];return v
    def xor(self,a,b):
        if a==b:return -1
        if a==-b:return 1
        if a==-1:return b
        if b==-1:return a
        if a==1:return -b
        if b==1:return -a
        v=self.fresh();self.clauses += [[-a,-b,-v],[a,b,-v],[a,-b,v],[-a,b,v]];return v
    def equal(self,a,b):self.clauses += [[-a,b],[a,-b]]

def build(n,factor,encoding='seqcounter',fixed=None,all_prefixes=False):
    c=Circuit();free=[c.fresh() for _ in range(n)]
    for j in range(n-1):c.clauses.append([free[j],free[j+1]])
    for j in range(n-4):c.clauses.append([-q for q in free[j:j+5]])
    rows=[[-1]*(2*n+1),[1 if t%2==0 else free[t//2] for t in range(2*n)]]
    for d in range(2,2*n+1):
        rows.append([c.xor(rows[d-1][t+1],c.lor(rows[d-1][t],rows[d-2][t])) for t in range(2*n-d+1)])
    E=[rows[2*d+2][0] for d in range(n)]
    initial=[c.fresh() for _ in range(2*n)];row=initial
    if fixed is not None:
        c.clauses += [[q if fixed>>j&1 else -q] for j,q in enumerate(initial)]
    for t in range(2*n-1):
        row=[c.xor((1 if t%2==0 else -1) if j==0 else row[j-1],c.lor(row[j],row[j+1])) for j in range(len(row)-1)]
        if t%2==0:c.equal(free[t//2],-row[0])
    # 3*black(E)<zeros(s) iff ones(s)+3*black(E)<=n-1.
    if all_prefixes:
        counter=[1]+[-1]*n;violations=[]
        for d in range(n):
            for lit in [free[d]]+[E[d]]*factor:
                counter=[1]+[c.lor(counter[j],-c.lor(-counter[j-1],-lit)) for j in range(1,n+1)]
            violations.append(-counter[d+1])
        c.clauses.append(violations)
        return c,free,E,initial
    count_lits=free[:]
    for e in E:
        count_lits.append(e)
        for _ in range(factor-1):
            clone=c.fresh();c.equal(clone,e);count_lits.append(clone)
    enc=CardEnc.atmost(count_lits,bound=n-1,top_id=c.nv,encoding=getattr(EncType,encoding))
    c.clauses.extend(enc.clauses);c.nv=enc.nv
    return c,free,E,initial

def solve(c,engine,seconds):
    with Solver(name=engine,bootstrap_with=c.clauses,use_timer=True) as solver:
        timer=threading.Timer(seconds,solver.interrupt);timer.daemon=True;timer.start()
        try:
            result=solver.solve_limited(expect_interrupt=True)
            model=set(solver.get_model()) if result else None;stats=solver.accum_stats()
        finally:timer.cancel()
    return result,model,stats

def validate(n,free,E,initial,model,factor,all_prefixes=False):
    f=[int(q in model) for q in free];e=sum(int(q in model)<<j for j,q in enumerate(E))
    R=sum(int(q in model)<<j for j,q in enumerate(initial));x=R;physical=[]
    for t in range(2*n-1):
        x=step(x,t)
        if t%2==0:physical.append(1^(x&1))
    assert physical==f and forbidden(f) is None and decode(e,n)==f and even_code(f)==e
    violations=[k for k in range(1,n+1) if factor*(e&((1<<k)-1)).bit_count()<f[:k].count(0)]
    assert violations if all_prefixes else factor*e.bit_count()<f.count(0)
    return {'free_prefix':f,'right_initial_hex':hex(R),'even_input_hex':hex(e),
            'free_zeros':f.count(0),'black_even_cells':e.bit_count(),'violating_prefixes':violations,
            'independent_physical_checks_passed':True}

def controls(engine):
    for a in [False,True]:
        for b in [False,True]:
            c=Circuit();x=c.fresh();y=c.fresh();o=c.lor(x,y);z=c.xor(x,y)
            c.clauses += [[x if a else -x],[y if b else -y],[-o if a or b else o]]
            assert solve(c,engine,5)[0] is False
            c=Circuit();x=c.fresh();y=c.fresh();z=c.xor(x,y)
            c.clauses += [[x if a else -x],[y if b else -y],[-z if a^b else z]]
            assert solve(c,engine,5)[0] is False
    for n,factor,fixed,expected in [(5,3,None,False),(11,2,None,True),(12,2,0x2de189,False)]:
        c,f,E,R=build(n,factor,fixed=fixed);result,m,_=solve(c,engine,8);assert result is expected
        if result:validate(n,f,E,R,m,factor)
    c,f,E,R=build(12,2,fixed=0x2de189,all_prefixes=True)
    result,m,_=solve(c,engine,8);assert result is True
    witness=validate(12,f,E,R,m,2,all_prefixes=True);assert witness['violating_prefixes']==[11]
    return {'boolean_gate_cases':8,'bounded_charge_cases':3,'recovering_prefix_control':True,'all_passed':True}

def main():
    p=argparse.ArgumentParser();p.add_argument('--length',type=int,default=96);p.add_argument('--factor',type=int,default=3)
    p.add_argument('--solver',default='g4');p.add_argument('--encoding',choices=['seqcounter','totalizer','cardnetwrk'],default='seqcounter')
    p.add_argument('--seconds',type=float,default=90);p.add_argument('--all-prefixes',action='store_true')
    a=p.parse_args();start=time.monotonic();checked=controls(a.solver)
    c,free,E,R=build(a.length,a.factor,a.encoding,all_prefixes=a.all_prefixes);result,m,stats=solve(c,a.solver,a.seconds)
    out={'length':a.length,'factor':a.factor,'engine':a.solver,'encoding':a.encoding,'python_sat_version':pysat.__version__,
         'solver_status':'sat' if result is True else 'unsat' if result is False else 'unknown_timeout',
         'actual_right_dynamics_enforced':True,'controls':checked,'variables':c.nv,'clauses':len(c.clauses),
         'every_prefix_checked':a.all_prefixes,
         'solver_stats':stats,'Lean_verified':False,'unbounded_charge_proved':False,'full_problem_solved':False}
    if result:out.update(validate(a.length,free,E,R,m,a.factor,a.all_prefixes))
    out['seconds']=round(time.monotonic()-start,3)
    save(f'coupled-charge-cnf-{a.length}-factor{a.factor}-{a.solver}-{a.encoding}'+('-prefixes' if a.all_prefixes else '')+'.json',out);print(out,flush=True)

if __name__=='__main__':main()
