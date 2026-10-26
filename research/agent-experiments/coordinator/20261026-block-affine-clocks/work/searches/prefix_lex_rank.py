"""Global word rank with reader state and nonlocal prefix parity/counters.
Unlike previous reader-only digits, a sink digit retains actual background bits.
Only a SAT certificate independently closed over every word could prove anything.
"""
from pathlib import Path
from collections import deque
import sys,time,json
r=Path(__file__).resolve().parent
sys.path.insert(0,r'D:\MWB\Rule30\wolfram-local\z3-deps')
import z3
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa']
START=time.monotonic();reports=[];candidate=None
def output(s,p,q):return (((s>>1)^((p>>1)|(q>>1)))<<1)|((s&1)^((p&1)|(q&1)))
def context_size(mode):return {'xor':4,'symbols':16,'count4':16,'indexxor':8}[mode]
def advance_context(mode,c,a):
    if mode=='xor':return c^a
    if mode=='symbols':return c^(1<<a)
    if mode=='count4':return (((c&3)+(a>>1))%4)|(((((c>>2)+(a&1))%4))<<2)
    return ((c^a)&3)|((1-(c>>2))<<2)
def build(context,K):
    C=context_size(context);initial=(0,0,*([0,0]*K),0,0,0)
    states=[initial];index={initial:0};edges=[];i=0
    while i<len(states):
        if len(states)>30000:return states,edges,False
        s=states[i];qr,qt=s[:2];cr,ct,last=s[-3:];row=[]
        for a in range(4):
            v=a;mem=[]
            for k in range(K):
                p,q=s[2+2*k:4+2*k];mem.extend([v,p]);v=output(v,p,q)
            nxt=(reader['transitions'][qr][a],reader['transitions'][qt][v],*mem,advance_context(context,cr,a),advance_context(context,ct,v),v)
            if nxt not in index:index[nxt]=len(states);states.append(nxt)
            row.append((index[nxt],(qr*C+cr)*4+a,(qt*C+ct)*4+v))
        edges.append(row);i+=1
        if time.monotonic()-START>140:return states,edges,False
    return states,edges,True
def target(s,K):return s[0]==15 and all(s[2+2*j] in [0,3] for j in range(K)) and s[-1] in [0,3]
def verify(states,edges,K,digits,direction):
    todo=deque([(0,1)]);seen={(0,1)};bad=None
    while todo:
        i,c=todo.popleft()
        if target(states[i],K) and c!=2:bad=(i,c);break
        for j,a,b in edges[i]:
            d=(digits[a]>digits[b])-(digits[a]<digits[b])
            if direction=='first' and c!=1:nc=c
            elif d:nc=2 if d>0 else 0
            else:nc=c
            if (j,nc) not in seen:seen.add((j,nc));todo.append((j,nc))
    return bad is None,len(seen),bad
for K in [1,2]:
    for context in ['xor','indexxor','symbols','count4']:
        states,edges,complete=build(context,K)
        if not complete:
            reports.append({'updates':K,'context':context,'states':len(states),'status':'graph_cap'});break
        for direction in ['first','last']:
            size=17*context_size(context)*4
            solver=z3.Solver();solver.set(timeout=6000,max_memory=1536)
            w=[z3.Int('w_'+str(j)) for j in range(size)]
            reach=[[z3.Bool(f'r_{j}_{c}') for c in range(3)] for j in range(len(states))]
            for d in w:solver.add(d>=0,d<size)
            solver.add(reach[0][1]);targets=0
            for i,s in enumerate(states):
                if target(s,K):
                    solver.add(z3.Not(reach[i][0]),z3.Not(reach[i][1]));targets+=1
                for j,a,b in edges[i]:
                    diff=w[a]-w[b]
                    for c in range(3):
                        if direction=='first' and c!=1:solver.add(z3.Implies(reach[i][c],reach[j][c]));continue
                        solver.add(z3.Implies(z3.And(reach[i][c],diff<0),reach[j][0]))
                        solver.add(z3.Implies(z3.And(reach[i][c],diff==0),reach[j][c]))
                        solver.add(z3.Implies(z3.And(reach[i][c],diff>0),reach[j][2]))
            begin=time.monotonic();status=solver.check()
            meta={'updates':K,'context':context,'direction':direction,'states':len(states),
                  'digit_variables':size,'targets':targets,'status':str(status),'seconds':round(time.monotonic()-begin,3)}
            if status==z3.sat:
                m=solver.model();digits=[m.eval(x).as_long() for x in w]
                ok,n,bad=verify(states,edges,K,digits,direction);assert ok,bad
                candidate={'digits':digits,'context':context,'updates':K,'direction':direction,
                           'graph_states':states,'graph_edges':edges,'closed_comparison_nodes':n}
                meta['independent_all_word_check_passed']=True
            if status==z3.unknown:meta['reason']=solver.reason_unknown()
            reports.append(meta);print(json.dumps(meta),flush=True)
            if candidate or time.monotonic()-START>140:break
        if candidate or time.monotonic()-START>140:break
    if candidate or time.monotonic()-START>140:break
out={'reports':reports,'candidate':candidate,'seconds':round(time.monotonic()-START,3),
     'Lean_verified':False,'sink_separation_proved':False,'full_problem_solved':False}
(r/'prefix-lex-rank.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'candidate_found':candidate is not None,'seconds':out['seconds']}),flush=True)
