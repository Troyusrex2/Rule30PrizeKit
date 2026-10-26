"""Exact periodic countermodels, with a selectable finite white prefix.
Inactive padding has no equations. SAT is independently replayed for a whole
cycle; UNSAT/unknown in these bounded instances is not an all-width theorem.
"""
from pathlib import Path
import json,time,sys
sys.path.insert(0,r'D:\MWB\Rule30\wolfram-local\z3-deps')
import z3
r=Path(__file__).resolve().parent;BEGIN=time.monotonic();reports=[];counter=None
def canonical(xs):
    i=next((i for i,x in enumerate(xs) if x),len(xs))
    return i>=len(xs)-2 or (i+3<len(xs) and xs[i+1]==xs[i+2])
def build(N,P,kind,canon=True,minwidth=4,fixed=None):
    solver=z3.Solver();solver.set(timeout=8000,max_memory=1536)
    active=[z3.Bool('active_'+str(j)) for j in range(N)]
    for j in range(minwidth):solver.add(active[j])
    for j in range(N-1):solver.add(z3.Implies(active[j+1],active[j]))
    ends=[z3.And(active[j],z3.Not(active[j+1])) if j+1<N else active[j] for j in range(N)]
    grids=[[[z3.Bool(f'a_{s}_{t}_{j}') for j in range(N)] for t in range(P)] for s in range(2 if kind=='pair' else 1)]
    for grid in grids:
        for t in range(P):
            for j in range(N):
                p=grid[t][j-1] if j else z3.BoolVal(False)
                q=grid[t][j-2] if j>=2 else z3.BoolVal(False)
                solver.add(z3.Implies(active[j],grid[(t+1)%P][j]==z3.Xor(grid[t][j],z3.Or(p,q))))
        if canon:
            xs=grid[0]
            core=z3.And([z3.Implies(active[j+2],z3.Not(xs[j])) for j in range(N-2)])
            noncore=z3.Or([z3.And(active[k+3],xs[k],xs[k+1]==xs[k+2],*[z3.Not(xs[i]) for i in range(k)]) for k in range(N-3)])
            solver.add(z3.Or(core,noncore))
    if kind=='pair':
        a,b=grids
        for j in range(minwidth-1,N):
            solver.add(z3.Implies(ends[j],a[0][j-1]!=b[0][j-1]))
            for t in range(P):solver.add(z3.Implies(ends[j],a[t][j]==b[t][j]))
    else:
        assert P%2==0
        a=grids[0]
        solver.add(z3.Or([z3.And(active[j],a[0][j]!=a[P//2][j]) for j in range(N)]))
        for j in range(minwidth-1,N):
            for t in range(P):solver.add(z3.Implies(ends[j],a[t][j]==a[(t+P//2)%P][j]))
    if fixed is not None:
        n=len(fixed[0]);assert all(len(x)==n for x in fixed) and len(fixed)==len(grids)
        for j in range(N):solver.add(active[j]==(j<n))
        for grid,initial in zip(grids,fixed):
            for j,x in enumerate(initial):solver.add(grid[0][j]==bool(x))
    return solver,active,grids
def audit(model,active,grids,P,kind,canon):
    flags=[z3.is_true(model.eval(x,model_completion=True)) for x in active]
    n=sum(flags);assert flags==[True]*n+[False]*(len(flags)-n)
    tables=[[[int(z3.is_true(model.eval(x,model_completion=True))) for x in row[:n]] for row in grid] for grid in grids]
    for table in tables:
        if canon:assert canonical(table[0])
        for t in range(P):
            old=table[t]
            new=[(30>>(4*x+2*(old[j-1] if j else 0)+(old[j-2] if j>=2 else 0)))&1 for j,x in enumerate(old)]
            assert new==table[(t+1)%P]
    if kind=='pair':
        a,b=tables;assert a[0][-2]!=b[0][-2]
        assert all(a[t][-1]==b[t][-1] for t in range(P))
    else:
        a=tables[0];assert a[0]!=a[P//2]
        assert all(a[t][-1]==a[(t+P//2)%P][-1] for t in range(P))
        if canon:assert canonical(a[P//2])
    return {'width':n,'period':P,'kind':kind,'canonical':canon,'initial_rows':[t[0] for t in tables],
            'tables':tables,'literal_full_cycle_audit_passed':True}
# Known equal traces with different raw parent bits; normalization must reject.
control=[]
for canon in [False,True]:
    s,active,grids=build(8,2,'pair',canon,minwidth=3,fixed=[[0,1,0],[1,0,0]])
    st=s.check();assert str(st)==('unsat' if canon else 'sat')
    if st==z3.sat:assert audit(s.model(),active,grids,2,'pair',canon)['width']==3
    control.append({'case':'raw_core_alias_with_inactive_padding','canonical':canon,'status':str(st)})
s,active,grids=build(8,4,'phase',True,minwidth=4,fixed=[[1,0,0,0]])
assert s.check()==z3.unsat
control.append({'case':'known_canonical_four_cycle_has_no_half_period_head','status':'unsat'})
for kind,N,P in [('phase',48,128),('pair',48,128),('phase',80,128),
                 ('pair',80,128),('phase',48,256),('pair',48,256)]:
    if time.monotonic()-BEGIN>140:break
    start=time.monotonic();s,active,grids=build(N,P,kind)
    built=time.monotonic();st=s.check()
    rec={'kind':kind,'maximum_width':N,'minimum_width':4,'cycle_clock':P,
         'status':str(st),'build_seconds':round(built-start,3),'solve_seconds':round(time.monotonic()-built,3)}
    if st==z3.sat:
        counter=audit(s.model(),active,grids,P,kind,True);rec['counterexample_width']=counter['width']
    if st==z3.unknown:rec['reason']=s.reason_unknown()
    reports.append(rec);print(json.dumps(rec),flush=True)
    out={'controls':control,'reports':reports,'counterexample':counter,
         'Lean_verified':False,'bounded_queries_only':True,'full_problem_solved':False}
    (r/'cyclic-counterexample.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    if counter:break
