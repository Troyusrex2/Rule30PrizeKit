"""Exact cyclic spacetime SAT; models checked by independent literal iteration."""
from pathlib import Path
import hashlib,json,sys,time,threading
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'sustained-math-20261028/vendor'))
def neg(a):return not a if isinstance(a,bool) else -a
class CNF:
    def __init__(self):self.n=0;self.cs=[]
    def var(self):self.n+=1;return self.n
    def clause(self,*lits):
        if any(x is True for x in lits):return
        clean=list(dict.fromkeys(x for x in lits if x is not False))
        if any(-x in clean for x in clean):return
        self.cs.append(clean)
    def either(self,a,b):
        c=self.var();self.clause(neg(a),c);self.clause(neg(b),c);self.clause(a,b,-c);return c
    def xor(self,a,b,out):
        self.clause(a,b,-out);self.clause(neg(a),neg(b),-out)
        self.clause(a,neg(b),out);self.clause(neg(a),b,out)
def period(xs):
    return next(h for h in range(1,len(xs)+1) if len(xs)%h==0 and all(xs[t]==xs[(t+h)%len(xs)] for t in range(len(xs))))
def encode(q,w,mode):
    e=CNF();x=[[e.var() for _ in range(q)] for _ in range(w)]
    for j in range(w):
        for t in range(q):
            if mode=='free' and j<2:continue
            if j==0:e.clause(x[0][t]);continue
            driver=x[j-1][t] if j==1 else e.either(x[j-1][t],x[j-2][t])
            e.xor(x[j][t],driver,x[j][(t+1)%q])
    if mode=='seed':
        for j in range(w):e.clause(x[j][0] if j==0 else -x[j][0])
    else:
        h=q//2;e.clause(-x[w-2][0]);e.clause(x[w-2][h])
        for t in range(h):
            a,b=x[w-1][t],x[w-1][t+h];e.clause(-a,b);e.clause(a,-b)
    return e,x
def worker(q,w,mode):
    from pysat.solvers import Solver
    import pysat
    start=time.monotonic();e,x=encode(q,w,mode);case=ROOT/f'{mode}-q{q}-w{w}';case.mkdir(exist_ok=False)
    text=f'p cnf {e.n} {len(e.cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in e.cs)
    (case/'input.cnf').write_text(text,encoding='ascii')
    with Solver(name='g4',bootstrap_with=e.cs,use_timer=True) as solver:
        timer=threading.Timer(3,solver.interrupt);timer.start()
        try:sat=solver.solve_limited(expect_interrupt=True)
        finally:timer.cancel();timer.join()
        out={'clock':q,'width':w,'mode':mode,'status':'SAT' if sat is True else 'UNSAT' if sat is False else 'UNKNOWN_INTERRUPT','seconds':time.monotonic()-start,'variables':e.n,'clauses':len(e.cs),'cnf_sha256':hashlib.sha256(text.encode('ascii')).hexdigest(),'solver':'glucose4','pysat':pysat.__version__,'stats':solver.accum_stats(),'kernel_verified':False}
        if sat:
            m=set(solver.get_model());assert all(any(lit in m for lit in c) for c in e.cs)
            cols=[[int(v in m) for v in col] for col in x];rows=[sum(cols[j][t]<<j for j in range(w)) for t in range(q)]
            if mode!='free':
                mask=(1<<w)-1
                assert all(((rows[t]^((rows[t]<<1)|(rows[t]<<2)))&mask)==rows[(t+1)%q] for t in range(q))
            else:
                assert all(cols[j][(t+1)%q]==(cols[j][t]^(cols[j-1][t] or cols[j-2][t])) for j in range(2,w) for t in range(q))
            ps=[period(c) for c in cols]
            if mode!='seed':assert ps[-2]==q and ps[-1]<=q//2
            out.update({'initial_word':rows[0],'column_periods':ps,'model_clauses_checked':True,'literal_cycle_checked':True,'genuine_white_boundary':mode!='free','rows':rows})
    (case/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
if __name__=='__main__':worker(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3])
