"""ICE learning of a nondeterministic regular invariant over cyclic profiles.
Subset construction is exact. Success requires complete seed and closure checks.
"""
from pathlib import Path
from collections import deque
from functools import lru_cache
import sys,json,time,threading
r=Path(__file__).resolve().parent
sys.path.insert(0,str(r.parents[2]/'toolchain/sat-research'))
from pysat.solvers import Minisat22
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa']
START=time.monotonic();MAX_SECONDS=170;MAX_CLAUSES=2500000;MAX_TRIE=20000
def difference(a):return ((a>>2)&1)!=(a&1)
def safe(q,w):return q!=15 or any(map(difference,w))
warm=json.loads((r/'ice-safe-samples.json').read_bytes())
positive={(q,tuple(w)) for q,w in warm['positive']}
negative={(q,tuple(w)) for q,w in warm['negative'] if safe(q,w)}
implications={(q,tuple(w),qp,tuple(wp)) for q,w,qp,wp in warm['implications']}
treewarm=json.loads((r/'ice-typed-samples.json').read_bytes());trees=treewarm['trees']
@lru_cache(maxsize=None)
def leaves(t):
    if t<16:return (t,)
    a,b=trees[t];return leaves(a)+leaves(b)
positive.update((q,leaves(t)) for q,t in treewarm['positive'])
negative.update((q,leaves(t)) for q,t in treewarm['negative'] if safe(q,leaves(t)))
implications.update((q,leaves(a),qp,leaves(b)) for q,a,qp,b in treewarm['implications'])
assert all(safe(q,w) for q,w in positive|negative)
assert all(safe(q,w) and safe(qp,wp) for q,w,qp,wp in implications)
def transform(w,c):
    x,y=c>>1,c&1;out=[]
    for a in w:
        u,v,up,vp=a>>3,(a>>2)&1,(a>>1)&1,a&1
        out.append((v<<3)|(x<<2)|(vp<<1)|y);x^=u|v;y^=up|vp
    return tuple(out),(x<<1)|y
def machine(m):
    @lru_cache(maxsize=200000)
    def step(s,a):
        out=0
        while s:
            low=s&-s;i=low.bit_length()-1;out|=m['delta'][a][i];s^=low
        return out
    def raw(q,w):
        s=1
        for a in w:s=step(s,a)
        return bool(s&m['accept'][q])
    return step,raw
def learn(K):
    trie=[{}];terminal={():0}
    def node(w):
        s=0
        for a in w:
            if a not in trie[s]:trie[s][a]=len(trie);trie.append({})
            s=trie[s][a]
        terminal[w]=s;return s
    tags=set(positive)|set(negative)
    tags.update((q,w) for q,w,_,_ in implications);tags.update((q,w) for _,_,q,w in implications)
    for q,w in sorted(tags):node(w)
    if len(trie)>MAX_TRIE:return None,{'status':'trie_cap','trie_nodes':len(trie)}
    estimate=(len(trie)-1)*(4*K*K+K)+len(tags)*(4*K+1)+5*K*len(trie)
    if estimate>MAX_CLAUSES:return None,{'status':'clause_estimate_cap','estimated_clauses':estimate}
    count=0
    def new():
        nonlocal count;count+=1;return count
    T=[[[new() for _ in range(K)] for _ in range(K)] for _ in range(16)]
    A=[[new() for _ in range(K)] for _ in range(17)]
    X=[[new() for _ in range(K)] for _ in trie];E={tag:new() for tag in tags};clauses=[]
    def both(x,y):
        z=new();clauses.extend([[-z,x],[-z,y],[z,-x,-y]]);return z
    def disjunction(z,ys):
        clauses.append([-z,*ys])
        for y in ys:clauses.append([-y,z])
    for i,v in enumerate(X[0]):clauses.append([v if i==0 else -v])
    for parent,edges in enumerate(trie):
        for a,child in edges.items():
            for j in range(K):disjunction(X[child][j],[both(X[parent][i],T[a][i][j]) for i in range(K)])
    for (q,w),e in E.items():disjunction(e,[both(X[terminal[w]][i],A[q][i]) for i in range(K)])
    for q,w in positive:clauses.append([E[q,w]])
    for q,w in negative:clauses.append([-E[q,w]])
    for q,w,qp,wp in implications:clauses.append([-E[q,w],E[qp,wp]])
    # Number states by the first sample-prefix set containing them; ties allowed.
    prev=None
    for xs in X:
        seen=[new() for _ in range(K)]
        for j in range(K):
            if prev is None:clauses.extend([[-seen[j],xs[j]],[-xs[j],seen[j]]])
            else:clauses.extend([[-prev[j],seen[j]],[-xs[j],seen[j]],[-seen[j],prev[j],xs[j]]])
            if j:clauses.append([-xs[j],seen[j-1]])
        prev=seen
    meta={'nfa_states':K,'trie_nodes':len(trie),'clauses':len(clauses),'variables':count}
    if len(clauses)>MAX_CLAUSES:return None,dict(meta,status='clause_cap')
    solver=Minisat22(bootstrap_with=clauses);timer=threading.Timer(10,solver.interrupt);timer.daemon=True
    t=time.monotonic();timer.start()
    try:status=solver.solve_limited(expect_interrupt=True)
    finally:timer.cancel()
    meta['solver_seconds']=round(time.monotonic()-t,3)
    if status is not True:
        solver.delete();return None,dict(meta,status='solver_interrupted' if status is None else 'unsat_at_state_bound')
    lits=set(solver.get_model());solver.delete()
    m={'delta':[[sum(1<<j for j,v in enumerate(row) if v in lits) for row in symbol] for symbol in T],
       'accept':[sum(1<<j for j,v in enumerate(row) if v in lits) for row in A]}
    step,raw=machine(m)
    assert all(raw(q,w) for q,w in positive)
    assert all(not raw(q,w) for q,w in negative)
    assert all(not raw(q,w) or raw(qp,wp) for q,w,qp,wp in implications)
    return m,dict(meta,status='sat')
def verify(m,limit=30):
    step,raw=machine(m);pos=[];impl=[];checked=0
    s=1;n=0;seen=set()
    while s not in seen:
        seen.add(s);s=step(s,0);n+=1
        if not (s&m['accept'][0]):pos.append((0,(0,)*n));break
    def acc(q,s,d):return bool(s&m['accept'][q]) and (q!=15 or d)
    def witness(par,v):
        out=[]
        while par[v] is not None:v,a=par[v];out.append(a)
        return tuple(reversed(out))
    for carry in range(4):
        initial=(1,1,carry,False,False,False);queue=deque([initial]);parent={initial:None};found=set()
        while queue:
            v=queue.popleft();s,t,c,di,do,nonempty=v;checked+=1
            if nonempty and c==carry:
                for q in range(17):
                    qp=reader['transitions'][q][carry]
                    if q not in found and acc(q,s,di) and not acc(qp,t,do):
                        w=witness(parent,v);wp,last=transform(w,carry)
                        assert last==carry and safe(q,w) and raw(q,w)
                        assert not safe(qp,wp) or not raw(qp,wp)
                        impl.append((q,w,qp,wp));found.add(q)
                        if len(impl)>=limit:return pos,impl,checked,False,None
            for a in range(16):
                u,x,up,xp=a>>3,(a>>2)&1,(a>>1)&1,a&1
                b=(x<<3)|((c>>1)<<2)|(xp<<1)|(c&1)
                cn=c^((u|x)<<1)^(up|xp)
                target=(step(s,a),step(t,b),cn,di or difference(a),do or difference(b),True)
                if target not in parent:parent[target]=(v,a);queue.append(target)
            if checked>1000000:return pos,impl,checked,False,'verification_node_cap'
            if time.monotonic()-START>MAX_SECONDS:return pos,impl,checked,False,'time_cap'
    return pos,impl,checked,True,None
history=[];K=2;success=None;reason=None
for iteration in range(200):
    if time.monotonic()-START>MAX_SECONDS:reason='time_cap';break
    if K>8:reason='state_bound_cap';break
    m,meta=learn(K);meta.update(iteration=iteration,positive=len(positive),negative=len(negative),implications=len(implications))
    if m is None:
        history.append(meta);print(json.dumps(meta),flush=True)
        if meta['status'] in ['trie_cap','clause_estimate_cap','clause_cap']:reason=meta['status'];break
        K+=1;continue
    p,i,checked,complete,cap=verify(m)
    meta.update(seed_counterexamples=len(p),closure_counterexamples=len(i),verification_nodes=checked,complete=complete)
    history.append(meta);print(json.dumps(meta),flush=True)
    (r/'nfa-latest-candidate.json').write_text(json.dumps(m,indent=2)+'\n',encoding='utf-8')
    if cap:reason=cap;break
    if not p and not i and complete:success=m;reason='candidate_invariant_all_nonempty_words';break
    before=len(positive)+len(negative)+len(implications);positive.update(p)
    for q,w,qp,wp in i:
        if not safe(qp,wp):negative.add((q,w))
        else:implications.add((q,w,qp,wp))
    assert len(positive)+len(negative)+len(implications)>before
else:reason='round_cap'
out={'history':history,'stop_reason':reason,'candidate_verified_by_python':success is not None,'candidate':success,
     'seconds':round(time.monotonic()-START,3),'Lean_verified':False,'full_problem_solved':False}
(r/'nfa-result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
(r/'nfa-samples.json').write_text(json.dumps({'positive':sorted(positive),'negative':sorted(negative),
 'implications':sorted(implications)},indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['history','candidate']}),flush=True)
