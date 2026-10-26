"""Typed dyadic invariant: individual cells and larger blocks have separate types.

This is a search, not a proof. Success requires repetition of an entire exact
height relation, seed closure, and no bad cyclic spatial extension.
"""
from pathlib import Path
from functools import lru_cache
import json, sys, time, threading
r=Path(__file__).resolve().parent
sys.path.insert(0,str(r.parents[2]/'toolchain/sat-research'))
from pysat.solvers import Minisat22
dfa=json.loads((r/'learned-reader.json').read_bytes())['dfa']
START=time.monotonic();MAX_SECONDS=160;MAX_TREE=25000;MAX_CLAUSES=2500000
warm=json.loads((r/'ice-sym-dyadic-samples.json').read_bytes())
trees=[tuple(t) if isinstance(t,list) else t for t in warm['trees']]
intern={t:i for i,t in enumerate(trees) if i>=16}
different=[((a>>2)&1)!=(a&1) for a in range(16)];heights=[0]*16
for l,h in trees[16:]:
    assert heights[l]==heights[h]
    heights.append(heights[l]+1);different.append(different[l] or different[h])
positive={tuple(t) for t in warm['positive']}
negative={tuple(t) for t in warm['negative']}
implications={tuple(t) for t in warm['implications']}
def node(a,b):
    assert heights[a]==heights[b]
    if (a,b) not in intern:
        if len(trees)>=MAX_TREE:raise RuntimeError('tree_dag_cap')
        intern[a,b]=len(trees);trees.append((a,b))
        heights.append(heights[a]+1);different.append(different[a] or different[b])
    return intern[a,b]
def decode(a):return a>>3,(a>>2)&1,(a>>1)&1,a&1
@lru_cache(maxsize=200000)
def transformed(t,c):
    if t<16:
        u,v,up,vp=decode(t);a,b=c>>1,c&1
        return (v<<3)|(a<<2)|(vp<<1)|b,((a^(u|v))<<1)|(b^(up|vp))
    l,h=trees[t];lt,mid=transformed(l,c);rt,end=transformed(h,mid)
    return node(lt,rt),end
def safe(q,t):return q!=15 or different[t]
def classify(m,t,cache):
    assert t>=16
    if t not in cache:
        a,b=trees[t]
        cache[t]=m['base'][a][b] if a<16 else m['join'][classify(m,a,cache)][classify(m,b,cache)]
    return cache[t]
def accepted(m,q,t,cache):
    return safe(q,t) and (m['leaf_accept'][q][t] if t<16 else m['accept'][q][classify(m,t,cache)])
def verify(m,limit=30):
    pos=[];neg=[];impl=[]
    if not m['leaf_accept'][0][0]:pos.append((0,0))
    s=m['base'][0][0];white=node(0,0);seen=set()
    while s not in seen:
        seen.add(s)
        if not m['accept'][0][s]:pos.append((0,white));break
        s=m['join'][s][s];white=node(white,white)
    def combine(height,a,b):
        if height==0:return 2*m['base'][a][b]+int(different[a] or different[b])
        return 2*m['join'][a//2][b//2]+int((a&1) or (b&1))
    def acc(height,q,s):
        if height==0:return m['leaf_accept'][q][s] and (q!=15 or different[s])
        return m['accept'][q][s//2] and (q!=15 or bool(s&1))
    deriv=[];current=[];ids={};initial=[];levels=[];signatures={}
    for a in range(16):
        for c in range(4):
            b,d=transformed(a,c);key=(a,b,c,d)
            if key not in ids:ids[key]=len(current);current.append(key);initial.append((a,b))
    deriv.append(initial)
    @lru_cache(maxsize=None)
    def witness(height,index):
        if height==0:return deriv[0][index]
        i,j=deriv[height][index]
        a,b=witness(height-1,i);ap,bp=witness(height-1,j)
        return node(a,ap),node(b,bp)
    attempts=0
    for height in range(24):
        signature=frozenset(current)
        if height>0 and signature in signatures:
            certificate={'relations_by_height':levels,'repeat_from_height':signatures[signature],
                         'repeat_at_height':height,'join_attempts':attempts}
            if not pos and not impl:
                (r/'typed-closure-certificate.json').write_text(json.dumps(certificate,indent=2)+'\n',encoding='utf-8')
            return pos,neg,impl,sum(map(len,levels)),True,None
        if height>0:signatures[signature]=height
        levels.append(current)
        for index,(s,t,c,d) in enumerate(current):
            if c!=d:continue
            for q in range(17):
                qp=dfa['transitions'][q][c]
                if acc(height,q,s) and not acc(height,qp,t):
                    a,b=witness(height,index);impl.append((q,a,qp,b))
                    if len(impl)>=limit:return pos,neg,impl,sum(map(len,levels)),False,None
        if impl:return pos,neg,impl,sum(map(len,levels)),False,None
        starts=[[] for _ in range(4)]
        for j,(_,_,c,_) in enumerate(current):starts[c].append(j)
        nxt=[];nids={};nd=[]
        for i,(s,t,c,d) in enumerate(current):
            for j in starts[d]:
                sp,tp,cp,dp=current[j]
                key=(combine(height,s,sp),combine(height,t,tp),c,dp);attempts+=1
                if key not in nids:nids[key]=len(nxt);nxt.append(key);nd.append((i,j))
            if attempts>4000000:return pos,neg,impl,sum(map(len,levels)),False,'join_attempt_cap'
            if time.monotonic()-START>MAX_SECONDS:return pos,neg,impl,sum(map(len,levels)),False,'time_cap'
        if len(nxt)>30000:return pos,neg,impl,sum(map(len,levels)),False,'relation_cap'
        current=nxt;deriv.append(nd)
    return pos,neg,impl,sum(map(len,levels)),False,'height_cap'
def learn(K):
    used=set();todo=[t for _,t in positive|negative]
    todo.extend(t for _,a,_,b in implications for t in (a,b))
    while todo:
        t=todo.pop()
        if t<16 or t in used:continue
        used.add(t);todo.extend(trees[t])
    used=sorted(used);upper=[t for t in used if heights[t]>1]
    tags=set(positive)|set(negative)
    tags.update((q,a) for q,a,_,_ in implications);tags.update((q,b) for _,_,q,b in implications)
    estimate=len(upper)*K**3+(len(upper)+256+K*K)*(K*(K-1)//2+1)+2*K*len(tags)+len(tags)+1
    if estimate>MAX_CLAUSES:return None,{'status':'clause_estimate_cap','estimated_clauses':estimate}
    count=0
    def fresh():
        nonlocal count;count+=1;return count
    L=[[fresh() for _ in range(16)] for _ in range(17)]
    A=[[fresh() for _ in range(K)] for _ in range(17)]
    B=[[[fresh() for _ in range(K)] for _ in range(16)] for _ in range(16)]
    J=[[[fresh() for _ in range(K)] for _ in range(K)] for _ in range(K)]
    X={t:(B[trees[t][0]][trees[t][1]] if heights[t]==1 else [fresh() for _ in range(K)]) for t in used}
    E={tag:(L[tag[0]][tag[1]] if tag[1]<16 else fresh()) for tag in tags};clauses=[]
    def one(xs):
        clauses.append(xs[:])
        for j,x in enumerate(xs):
            for y in xs[j+1:]:clauses.append([-x,-y])
    for row in B+J:
        for xs in row:one(xs)
    for t in upper:one(X[t])
    clauses.append([B[0][0][0]])
    # Canonical first-occurrence numbering; this only renames states.
    prev=None
    for xs in [v for row in B for v in row]+[X[t] for t in upper]:
        seen=[fresh() for _ in range(K)]
        for j in range(K):
            if prev is None:
                clauses.extend([[-seen[j],xs[j]],[-xs[j],seen[j]]])
                if j:clauses.append([-xs[j]])
            else:
                clauses.extend([[-prev[j],seen[j]],[-xs[j],seen[j]],[-seen[j],prev[j],xs[j]]])
                if j:clauses.append([-xs[j],prev[j-1]])
        prev=seen
    for t in upper:
        l,h=trees[t]
        for a in range(K):
            for b in range(K):
                for c in range(K):clauses.append([-X[l][a],-X[h][b],-J[a][b][c],X[t][c]])
    for (q,t),e in E.items():
        if t<16:continue
        for s in range(K):clauses.extend([[-X[t][s],-e,A[q][s]],[-X[t][s],e,-A[q][s]]])
    for q,t in positive:clauses.append([E[q,t]])
    for q,t in negative:clauses.append([-E[q,t]])
    for q,a,qp,b in implications:clauses.append([-E[q,a],E[qp,b]])
    meta={'states_above_leaves':K,'sample_tree_nodes':len(used),'sample_upper_nodes':len(upper),
          'clauses':len(clauses),'variables':count}
    solver=Minisat22(bootstrap_with=clauses);timer=threading.Timer(10,solver.interrupt);timer.daemon=True
    begin=time.monotonic();timer.start()
    try:result=solver.solve_limited(expect_interrupt=True)
    finally:timer.cancel()
    meta['solver_seconds']=round(time.monotonic()-begin,3)
    if result is not True:
        solver.delete();return None,dict(meta,status='solver_interrupted' if result is None else 'unsat_at_state_bound')
    literals=set(solver.get_model());solver.delete()
    def pick(xs):return next(i for i,v in enumerate(xs) if v in literals)
    m={'leaf_accept':[[v in literals for v in xs] for xs in L],
       'base':[[pick(xs) for xs in row] for row in B],
       'join':[[pick(xs) for xs in row] for row in J],
       'accept':[[v in literals for v in xs] for xs in A]}
    cache={}
    assert all(accepted(m,q,t,cache) for q,t in positive)
    assert all(not accepted(m,q,t,cache) for q,t in negative)
    assert all(not accepted(m,q,a,cache) or accepted(m,qp,b,cache) for q,a,qp,b in implications)
    return m,dict(meta,status='sat')
history=[];K=2;success=None;stop=None
try:
    for iteration in range(300):
        if time.monotonic()-START>MAX_SECONDS:stop='time_cap';break
        if K>16:stop='state_bound_cap';break
        m,meta=learn(K);meta.update(iteration=iteration,positive=len(positive),negative=len(negative),implications=len(implications))
        if m is None:
            history.append(meta);print(json.dumps(meta),flush=True)
            if meta['status']=='clause_estimate_cap':stop=meta['status'];break
            K+=1;continue
        p,n,i,nr,complete,cap=verify(m)
        meta.update(seed_counterexamples=len(p),closure_counterexamples=len(i),relation_states=nr,complete=complete)
        history.append(meta);print(json.dumps(meta),flush=True)
        if cap:stop=cap;break
        (r/'typed-latest-candidate.json').write_text(json.dumps(m,indent=2)+'\n',encoding='utf-8')
        if not p and not n and not i and complete:success=m;stop='candidate_invariant_all_dyadic_heights';break
        old=len(positive)+len(negative)+len(implications);positive.update(p)
        for q,a,qp,b in i:
            assert safe(q,a)
            if not safe(qp,b):negative.add((q,a))
            else:implications.add((q,a,qp,b))
        assert len(positive)+len(negative)+len(implications)>old
    else:stop='round_cap'
except RuntimeError as e:stop=str(e)
out={'history':history,'stop_reason':stop,'candidate_verified_by_python':success is not None,'candidate':success,
     'tree_dag_nodes':len(trees),'seconds':round(time.monotonic()-START,3),'Lean_verified':False,
     'reader_completeness_proved':False,'full_problem_solved':False}
(r/'ice-typed.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
(r/'ice-typed-samples.json').write_text(json.dumps({'trees':trees,'positive':sorted(positive),'negative':sorted(negative),
    'implications':sorted(implications)},indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['history','candidate']}),flush=True)
