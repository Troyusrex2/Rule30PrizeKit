"""Regular tree invariant search specialized to perfect dyadic clocks.
Success requires exact repetition of the entire finite relation by height.
No finite tested height alone establishes unbounded closure.
"""
from pathlib import Path
from collections import deque
from functools import lru_cache
import json,sys,time,threading
r=Path(__file__).resolve().parent
sys.path.insert(0,str(r.parents[2]/'toolchain/sat-research'))
from pysat.solvers import Minisat22
dfa=json.loads((r/'learned-reader.json').read_bytes())['dfa'];START=time.monotonic()
MAX_SECONDS=150;MAX_TREE=25000;MAX_CLAUSES=2000000;MAX_REL=20000
trees=list(range(16));intern={};different=[((a>>2)&1)!=(a&1) for a in range(16)]
def node(a,b):
    key=(a,b)
    if key not in intern:
        if len(trees)>MAX_TREE:raise RuntimeError('tree_dag_cap')
        intern[key]=len(trees);trees.append(key);different.append(different[a] or different[b])
    return intern[key]
def tree(word):
    if len(word)==1:return word[0]
    h=len(word)//2;return node(tree(word[:h]),tree(word[h:]))
def decode(a):return a>>3,(a>>2)&1,(a>>1)&1,a&1
def enc(a,b,c,d):return (a<<3)|(b<<2)|(c<<1)|d
@lru_cache(maxsize=200000)
def transformed(t,c):
    if t<16:
        u,v,up,vp=decode(t);a,b=c>>1,c&1
        return enc(v,a,vp,b),((a^(u|v))<<1)|(b^(up|vp))
    l,h=trees[t];lt,mid=transformed(l,c);rt,end=transformed(h,mid)
    return node(lt,rt),end
def safe(q,t):return q!=15 or different[t]
samples=json.loads((r/'ice-safe-samples.json').read_bytes())
power2=lambda n:n>0 and n&(n-1)==0
positive={(q,tree(tuple(w))) for q,w in samples['positive'] if power2(len(w))};positive.add((0,0))
negative={(q,tree(tuple(w))) for q,w in samples['negative'] if power2(len(w)) and (q!=15 or any(((a>>2)&1)!=(a&1) for a in w))}
implications=set()
for q,w,qp,wp in samples['implications']:
    if not power2(len(w)):continue
    a,b=tree(tuple(w)),tree(tuple(wp));assert safe(q,a) and safe(qp,b)
    implications.add((q,a,qp,b))
def classify(m,t,cache):
    if t in cache:return cache[t]
    if t<16:answer=m['leaf'][t]
    else:
        a,b=trees[t];answer=m['join'][classify(m,a,cache)][classify(m,b,cache)]
    cache[t]=answer;return answer
def accepted(m,q,t,cache):return safe(q,t) and m['accept'][q][classify(m,t,cache)]
def verify(m,limit=20):
    K=len(m['join']);pos=[];neg=[];impl=[]
    def leaf(a):return 2*m['leaf'][a]+int(different[a])
    def join(a,b):return 2*m['join'][a//2][b//2]+int((a&1) or (b&1))
    def acc(q,s):return m['accept'][q][s//2] and (q!=15 or bool(s&1))
    # Seed roots at heights 0,1,2,... are a finite deterministic orbit.
    seeds={};h=0;s=leaf(0);white=0
    while s not in seeds:
        seeds[s]=h
        if not acc(0,s):pos.append((0,white));break
        s=join(s,s);white=node(white,white);h+=1
    levels=[];deriv=[];signatures={}
    current=[];ids={};initial=[]
    for a in range(16):
        for c in range(4):
            b,d=transformed(a,c);key=(leaf(a),leaf(b),c,d)
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
        if signature in signatures:
            certificate={'relations_by_height':levels,'repeat_from_height':signatures[signature],
                         'repeat_at_height':height,'join_attempts':attempts}
            if not pos and not impl:
                (r/'dyadic-closure-certificate.json').write_text(json.dumps(certificate,indent=2)+'\n',encoding='utf-8')
            return pos,neg,impl,sum(map(len,levels)),True,None
        signatures[signature]=height;levels.append(current)
        for index,(s,t,c,d) in enumerate(current):
            if c!=d:continue
            for q in range(17):
                qp=dfa['transitions'][q][c]
                if acc(q,s) and not acc(qp,t):
                    a,b=witness(height,index);impl.append((q,a,qp,b))
                    if len(impl)>=limit:return pos,neg,impl,sum(map(len,levels)),False,None
        if impl:return pos,neg,impl,sum(map(len,levels)),False,None
        starts=[[] for _ in range(4)]
        for j,(_,_,c,_) in enumerate(current):starts[c].append(j)
        nxt=[];nids={};nd=[]
        for i,(s,t,c,d) in enumerate(current):
            for j in starts[d]:
                sp,tp,cp,dp=current[j];key=(join(s,sp),join(t,tp),c,dp);attempts+=1
                if key not in nids:nids[key]=len(nxt);nxt.append(key);nd.append((i,j))
            if attempts>3000000:return pos,neg,impl,sum(map(len,levels)),False,'join_attempt_cap'
            if time.monotonic()-START>MAX_SECONDS:return pos,neg,impl,sum(map(len,levels)),False,'time_cap'
        if len(nxt)>MAX_REL:return pos,neg,impl,sum(map(len,levels)),False,'relation_cap'
        current=nxt;deriv.append(nd)
    return pos,neg,impl,sum(map(len,levels)),False,'height_cap'
def learn(K):
    used=set(range(16));todo=[t for _,t in positive|negative]
    todo.extend(t for _,a,_,b in implications for t in (a,b))
    while todo:
        t=todo.pop()
        if t in used:continue
        used.add(t)
        if t>=16:todo.extend(trees[t])
    used=sorted(used);internals=[t for t in used if t>=16]
    tags=set(positive)|set(negative)
    tags.update((q,a) for q,a,_,_ in implications);tags.update((q,b) for _,_,q,b in implications)
    estimate=len(internals)*K**3+len(used)*(K*(K-1)//2+1)+K*K*(K*(K-1)//2+1)+2*K*len(tags)+len(tags)+1
    if estimate>MAX_CLAUSES:return None,{'status':'clause_estimate_cap','estimated_clauses':estimate}
    count=0
    def fresh():
        nonlocal count;count+=1;return count
    A=[[fresh() for _ in range(K)] for _ in range(17)]
    J=[[[fresh() for _ in range(K)] for _ in range(K)] for _ in range(K)]
    X={t:[fresh() for _ in range(K)] for t in used};E={tag:fresh() for tag in tags};clauses=[]
    def one(xs):
        clauses.append(xs[:])
        for j,x in enumerate(xs):
            for y in xs[j+1:]:clauses.append([-x,-y])
    for row in J:
        for xs in row:one(xs)
    for xs in X.values():one(xs)
    clauses.append([X[0][0]])
    for t in internals:
        l,h=trees[t]
        for a in range(K):
            for b in range(K):
                for c in range(K):clauses.append([-X[l][a],-X[h][b],-J[a][b][c],X[t][c]])
    for (q,t),e in E.items():
        for s in range(K):clauses.extend([[-X[t][s],-e,A[q][s]],[-X[t][s],e,-A[q][s]]])
    for q,t in positive:clauses.append([E[q,t]])
    for q,t in negative:clauses.append([-E[q,t]])
    for q,a,qp,b in implications:clauses.append([-E[q,a],E[qp,b]])
    meta={'states':K,'sample_tree_nodes':len(used),'clauses':len(clauses),'variables':count}
    solver=Minisat22(bootstrap_with=clauses);timer=threading.Timer(10,solver.interrupt);timer.daemon=True
    begin=time.monotonic();timer.start()
    try:result=solver.solve_limited(expect_interrupt=True)
    finally:timer.cancel()
    meta['solver_seconds']=round(time.monotonic()-begin,3)
    if result is not True:
        solver.delete();return None,dict(meta,status='solver_interrupted' if result is None else 'unsat_at_state_bound')
    literals=set(solver.get_model());solver.delete()
    m={'leaf':[next(i for i in range(K) if X[t][i] in literals) for t in range(16)],
       'join':[[next(c for c in range(K) if J[a][b][c] in literals) for b in range(K)] for a in range(K)],
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
        if K>10:stop='state_bound_cap';break
        m,meta=learn(K);meta.update(iteration=iteration,positive=len(positive),negative=len(negative),implications=len(implications))
        if m is None:
            history.append(meta);print(json.dumps(meta),flush=True)
            if meta['status']=='clause_estimate_cap':stop=meta['status'];break
            K+=1;continue
        p,n,i,nr,complete,cap=verify(m)
        meta.update(seed_counterexamples=len(p),closure_counterexamples=len(i),relation_states=nr,complete=complete)
        history.append(meta);print(json.dumps(meta),flush=True)
        if cap:stop=cap;break
        (r/'dyadic-latest-candidate.json').write_text(json.dumps(m,indent=2)+'\n',encoding='utf-8')
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
(r/'ice-dyadic.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
(r/'ice-dyadic-samples.json').write_text(json.dumps({'trees':trees,'positive':sorted(positive),'negative':sorted(negative),
    'implications':sorted(implications)},indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['history','candidate']}),flush=True)
