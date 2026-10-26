"""ICE learning of a regular invariant over cyclic temporal profile words.
Only a complete all-word seed/closure/safety check is a candidate success.
State bounds, solver interruption and resource caps are UNKNOWN, not proofs.
"""
from pathlib import Path
from collections import deque
import json,sys,time,threading,random
r=Path(__file__).resolve().parent
sys.path.insert(0,str(r.parents[2]/'toolchain/sat-research'))
from pysat.solvers import Minisat22
dfa=json.loads((r/'learned-reader.json').read_bytes())['dfa']
START=time.monotonic();MAX_SECONDS=150;MAX_CLAUSES=2000000;MAX_TRIE=30000;MAX_ROUNDS=100
positive={(0,(0,)),(0,(0,0))};negative=set();implications=set();history=[]
def decode(a):return (a>>3,(a>>2)&1,(a>>1)&1,a&1)
def encode(a,b,c,d):return (a<<3)|(b<<2)|(c<<1)|d
BAD=[a for a in range(16) if decode(a)[1]==decode(a)[3]]
negative.update((15,(a,)) for a in BAD)
for P in [2,4,8]:
    data=json.loads((r/f'clock-product-{P}-graph.json').read_bytes())['states']
    sample=data if P<8 else random.Random(508).sample(data,min(128,len(data)))
    for u,v,up,vp,q in sample:
        word=tuple(encode((u>>t)&1,(v>>t)&1,(up>>t)&1,(vp>>t)&1) for t in range(P))
        positive.add((q,word))
def transform(word,carry):
    ca,cb=carry>>1,carry&1;out=[]
    for a in word:
        u,v,up,vp=decode(a);out.append(encode(v,ca,vp,cb));ca^=u|v;cb^=up|vp
    return tuple(out),(ca<<1)|cb
def run(model,q,word):
    s=model['starts'][q]
    for a in word:s=model['delta'][s][a]
    return model['accepting'][s]
def reconstruct(parent,node):
    word=[]
    while parent[node] is not None:
        node,a=parent[node];word.append(a)
    return tuple(reversed(word))
def verify(model,limit=20):
    # Every nonempty all-white cyclic word must be included.
    s=model['starts'][0];seen=set();n=0;pos=[];neg=[];impl=[]
    while s not in seen:
        seen.add(s);s=model['delta'][s][0];n+=1
        if not model['accepting'][s]:pos.append((0,(0,)*n));break
    # Exclude every state-15 word whose current columns are identical.
    start=(model['starts'][15],False);queue=deque([start]);parent={start:None}
    while queue:
        node=queue.popleft();s,nonempty=node
        if nonempty and model['accepting'][s]:neg.append((15,reconstruct(parent,node)));break
        for a in BAD:
            target=(model['delta'][s][a],True)
            if target not in parent:parent[target]=(node,a);queue.append(target)
    # Exact all-word cyclic transducer closure, for each tag and initial carry.
    checked=0
    for q in range(17):
        for carry in range(4):
            qp=dfa['transitions'][q][carry];ca,cb=carry>>1,carry&1
            start=(model['starts'][q],model['starts'][qp],ca,cb,False)
            queue=deque([start]);parent={start:None};found=None
            while queue:
                node=queue.popleft();s,t,wa,wb,nonempty=node;checked+=1
                if nonempty and (wa,wb)==(ca,cb) and model['accepting'][s] and not model['accepting'][t]:
                    word=reconstruct(parent,node);output,last=transform(word,carry)
                    assert last==carry and run(model,q,word) and not run(model,qp,output)
                    found=(q,word,qp,output);break
                for a in range(16):
                    u,v,up,vp=decode(a);b=encode(v,wa,vp,wb)
                    target=(model['delta'][s][a],model['delta'][t][b],wa^(u|v),wb^(up|vp),True)
                    if target not in parent:parent[target]=(node,a);queue.append(target)
            if found is not None:impl.append(found)
            if len(impl)>=limit:return pos,neg,impl,checked,False
    return pos,neg,impl,checked,True
def learn(K):
    # Prefix-tree samples, separate roots for the 17 spatial DFA tags.
    trie=[{} for _ in range(17)];term={}
    def node(q,w):
        at=q
        for a in w:
            if a not in trie[at]:trie[at][a]=len(trie);trie.append({})
            at=trie[at][a]
        return at
    for q,w in positive|negative:node(q,w)
    for q,w,qp,wp in implications:node(q,w);node(qp,wp)
    if len(trie)>MAX_TRIE:return None,{'status':'trie_cap','nodes':len(trie)}
    count=0
    def new():
        nonlocal count;count+=1;return count
    accept=[new() for _ in range(K)]
    delta=[[[new() for _ in range(K)] for _ in range(16)] for _ in range(K)]
    where=[[new() for _ in range(K)] for _ in trie];end=[new() for _ in trie]
    clauses=[]
    def one(xs):
        clauses.append(xs[:])
        for j,x in enumerate(xs):
            for y in xs[j+1:]:clauses.append([-x,-y])
    for s in range(K):
        for a in range(16):one(delta[s][a])
    for xs in where:one(xs)
    clauses.append([where[0][0]])
    for p,trans in enumerate(trie):
        for s in range(K):
            clauses.extend([[-where[p][s],-end[p],accept[s]],[-where[p][s],end[p],-accept[s]]])
        for a,child in trans.items():
            for s in range(K):
                for t in range(K):clauses.append([-where[p][s],-delta[s][a][t],where[child][t]])
    for q,w in positive:clauses.append([end[node(q,w)]])
    for q,w in negative:clauses.append([-end[node(q,w)]])
    for q,w,qp,wp in implications:clauses.append([-end[node(q,w)],end[node(qp,wp)]])
    meta={'states':K,'trie_nodes':len(trie),'variables':count,'clauses':len(clauses)}
    if len(clauses)>MAX_CLAUSES:return None,dict(meta,status='clause_cap')
    solver=Minisat22(bootstrap_with=clauses);timer=threading.Timer(10,solver.interrupt);timer.daemon=True
    begin=time.monotonic();timer.start()
    try:result=solver.solve_limited(expect_interrupt=True)
    finally:timer.cancel()
    meta['solver_seconds']=round(time.monotonic()-begin,3)
    if result is None:solver.delete();return None,dict(meta,status='solver_interrupted')
    if result is False:solver.delete();return None,dict(meta,status='unsat_at_state_bound')
    literals=set(solver.get_model());solver.delete()
    model={'starts':[next(s for s in range(K) if where[q][s] in literals) for q in range(17)],
           'accepting':[x in literals for x in accept],
           'delta':[[next(t for t in range(K) if delta[s][a][t] in literals) for a in range(16)] for s in range(K)]}
    assert all(run(model,q,w) for q,w in positive)
    assert all(not run(model,q,w) for q,w in negative)
    assert all(not run(model,q,w) or run(model,qp,wp) for q,w,qp,wp in implications)
    return model,dict(meta,status='sat')
K=2;success=None;stop=None
for iteration in range(MAX_ROUNDS):
    if time.monotonic()-START>MAX_SECONDS:stop='time_cap';break
    if K>16:stop='state_bound_cap';break
    model,meta=learn(K);meta.update(iteration=iteration,positive=len(positive),negative=len(negative),implications=len(implications))
    if model is None:
        history.append(meta);print(json.dumps(meta),flush=True)
        if meta['status'] in ['trie_cap','clause_cap']:stop=meta['status'];break
        K+=1;continue
    p,n,i,checked,complete=verify(model)
    meta.update(seed_counterexamples=len(p),safety_counterexamples=len(n),closure_counterexamples=len(i),
                verification_nodes=checked,all_closure_cases_checked=complete)
    history.append(meta);print(json.dumps(meta),flush=True)
    (r/'latest-candidate.json').write_text(json.dumps(model,indent=2)+'\n',encoding='utf-8')
    if not p and not n and not i and complete:
        success=model;stop='candidate_invariant_all_words';break
    old=len(positive)+len(negative)+len(implications)
    positive.update(p);negative.update(n);implications.update(i)
    assert len(positive)+len(negative)+len(implications)>old
    (r/'ice-progress.json').write_text(json.dumps({'history':history,'candidate_verified':False},indent=2)+'\n',encoding='utf-8')
else:stop='round_cap'
out={'history':history,'stop_reason':stop,'candidate_verified_by_python':success is not None,
     'candidate':success,'seconds':round(time.monotonic()-START,3),'Lean_verified':False,
     'reader_completeness_proved':False,'full_problem_solved':False}
(r/'ice-invariant.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
samples={'positive':[[q,list(w)] for q,w in sorted(positive)],'negative':[[q,list(w)] for q,w in sorted(negative)],
         'implications':[[q,list(w),qp,list(wp)] for q,w,qp,wp in sorted(implications)]}
(r/'ice-samples.json').write_text(json.dumps(samples,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['history','candidate']}),flush=True)
