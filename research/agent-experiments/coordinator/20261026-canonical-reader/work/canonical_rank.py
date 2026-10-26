"""Try well-founded lexicographic word ranks on canonical configurations only.
The domain restriction has an all-width Lean existence/uniqueness certificate.
No solution of this finite synthesis problem means no theorem was obtained.
"""
from pathlib import Path
from collections import deque
import sys,time,json
r=Path(__file__).resolve().parent
sys.path.insert(0,r'D:\MWB\Rule30\wolfram-local\z3-deps')
import z3
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa'];T=reader['transitions']
C=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]];CA={0,1,2,3,5}
START=time.monotonic();reports=[];candidate=None
def output(s,p,q):return (((s>>1)^((p>>1)|(q>>1)))<<1)|((s&1)^((p&1)|(q&1)))
def build(context,K):
    base=4**context
    # Raw and K-step reader/canonical states, K two-symbol memories, contexts, last.
    initial=(0,0,0,0,0,0,*([0,0]*K),0,0,0)
    states=[initial];index={initial:0};edges=[];i=0;keys={}
    def digit(q,ca,cb,ctx,s):
        key=(q,ca,cb,ctx,s)
        if key not in keys:keys[key]=len(keys)
        return keys[key]
    while i<len(states):
        if len(states)>24000 or time.monotonic()-START>140:return states,edges,keys,False
        st=states[i];qr,qt,car,cbr,cat,cbt=st[:6];cr,ct,last=st[-3:];row=[]
        for a in range(4):
            na,nb=C[car][a>>1],C[cbr][a&1]
            if 6 in [na,nb]:continue
            v=a;mem=[]
            for k in range(K):
                p,q=st[6+2*k:8+2*k];mem.extend([v,p]);v=output(v,p,q)
            nxt=(T[qr][a],T[qt][v],na,nb,C[cat][v>>1],C[cbt][v&1],*mem,(4*cr+a)%base,(4*ct+v)%base,v)
            if nxt not in index:index[nxt]=len(states);states.append(nxt)
            row.append((index[nxt],digit(qr,car,cbr,cr,a),digit(qt,cat,cbt,ct,v)))
        edges.append(row);i+=1
    return states,edges,keys,True
def target(st,K):return st[0]==15 and st[2] in CA and st[3] in CA and all(st[6+2*j] in [0,3] for j in range(K)) and st[-1] in [0,3]
def verify(states,edges,K,digits,direction):
    todo=deque([(0,1)]);seen={(0,1)}
    while todo:
        i,c=todo.popleft()
        if target(states[i],K) and c!=2:return False,len(seen),(i,c)
        for j,a,b in edges[i]:
            d=(digits[a]>digits[b])-(digits[a]<digits[b])
            if direction=='first' and c!=1:nc=c
            elif d:nc=2 if d>0 else 0
            else:nc=c
            if (j,nc) not in seen:seen.add((j,nc));todo.append((j,nc))
    return True,len(seen),None
for K in [1,2,3]:
  for context in [0,1,2]:
    states,edges,keys,complete=build(context,K)
    if not complete:
      reports.append({'updates':K,'context':context,'states':len(states),'status':'graph_cap'});break
    for direction in ['first','last']:
      size=len(keys);solver=z3.Solver();solver.set(timeout=6000,max_memory=1024)
      w=[z3.Int('w_'+str(j)) for j in range(size)]
      reach=[[z3.Bool(f'r_{j}_{c}') for c in range(3)] for j in range(len(states))]
      for d in w:solver.add(d>=0,d<size)
      solver.add(reach[0][1]);targets=0
      for i,st in enumerate(states):
        if target(st,K):
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
        candidate={'digits':digits,'digit_keys':[[list(k),v] for k,v in keys.items()],
                   'context':context,'updates':K,'direction':direction,'graph_states':states,
                   'graph_edges':edges,'closed_comparison_nodes':n}
        meta['independent_all_word_check_passed']=True
      if status==z3.unknown:meta['reason']=solver.reason_unknown()
      reports.append(meta);print(json.dumps(meta),flush=True)
      if candidate or time.monotonic()-START>140:break
    if candidate or time.monotonic()-START>140:break
  if candidate or time.monotonic()-START>140:break
out={'reports':reports,'candidate':candidate,'seconds':round(time.monotonic()-START,3),
     'Lean_verified':False,'sink_separation_proved':False,'full_problem_solved':False}
(r/'canonical-rank.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'candidate_found':candidate is not None,'seconds':out['seconds']}),flush=True)
