"""Try lexicographic digit ranks, allowing exponential rather than linear delay."""
from pathlib import Path
import json,sys,time
sys.path.insert(0,r'D:\MWB\Rule30\wolfram-local\z3-deps')
import z3
ROOT=Path(__file__).resolve().parent
dfa=json.loads((ROOT/'learned-reader.json').read_bytes())['dfa']
def output(sym,p,q):return (((sym>>1)^((p>>1)|(q>>1)))<<1)|((sym&1)^((p&1)|(q&1)))
def graph(K):
    states=[(0,0,*([0,0]*K),0)];index={states[0]:0};edges=[];at=0
    while at<len(states):
        s=states[at];a,b=s[:2];row=[]
        for sym in range(4):
            value=sym;mem=[]
            for i in range(K):p,q=s[2+2*i:4+2*i];mem.extend([value,p]);value=output(value,p,q)
            nxt=(dfa['transitions'][a][sym],dfa['transitions'][b][value],*mem,value)
            if nxt not in index:index[nxt]=len(states);states.append(nxt)
            row.append((index[nxt],value))
        edges.append(row);at+=1
    return states,edges
reports=[]
for K in [1,2,3]:
    states,edges=graph(K)
    for direction in ['first_digit_dominates','last_digit_dominates']:
        solver=z3.Solver();solver.set(timeout=6000,max_memory=1536)
        w=[[z3.Int(f'w_{i}_{j}') for j in range(4)] for i in range(17)]
        reach=[[z3.Bool(f'r_{i}_{c}') for c in range(3)] for i in range(len(states))] # less,equal,greater
        for row in w:
            for x in row:solver.add(x>=0,x<=67)
        solver.add(reach[0][1])
        for i,s in enumerate(states):
            a,b=s[:2]
            bad=a not in dfa['accepting'] and all(s[2+2*j] in [0,3] for j in range(K)) and s[-1] in [0,3]
            if bad:solver.add(z3.Not(reach[i][0]),z3.Not(reach[i][1]))
            for sym,(j,out) in enumerate(edges[i]):
                diff=w[a][sym]-w[b][out]
                for c in range(3):
                    if direction=='first_digit_dominates' and c!=1:
                        solver.add(z3.Implies(reach[i][c],reach[j][c]));continue
                    solver.add(z3.Implies(z3.And(reach[i][c],diff<0),reach[j][0]))
                    solver.add(z3.Implies(z3.And(reach[i][c],diff==0),reach[j][c]))
                    solver.add(z3.Implies(z3.And(reach[i][c],diff>0),reach[j][2]))
        begin=time.monotonic();status=solver.check()
        r={'updates':K,'direction':direction,'states':len(states),'status':str(status),'seconds':round(time.monotonic()-begin,3)}
        if status==z3.sat:
            m=solver.model();r['digits']=[[m.eval(x).as_long() for x in row] for row in w]
            r['reachable_comparisons']=[[c for c,x in enumerate(row) if z3.is_true(m.eval(x))] for row in reach]
        elif status==z3.unknown:r['reason_unknown']=solver.reason_unknown()
        reports.append(r);print(json.dumps(r),flush=True)
        if status==z3.sat:break
    if reports[-1]['status']=='sat':break
(ROOT/'lex-rank.json').write_text(json.dumps({'reports':reports,'Lean_verified':False,'completeness_proved':False},indent=2)+'\n',encoding='utf-8')
