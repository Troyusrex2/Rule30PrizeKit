from pathlib import Path
import sys,json,time,hashlib,collections,subprocess
ROOT=Path(__file__).resolve().parent;started=time.monotonic()
SOLVER=Path('C:/Users/troyu/Rule30-offload/_cache/payload/toolchain/bin/cadical.exe')
class CNF:
    def __init__(self):self.n=0;self.clauses=[]
    def var(self):self.n+=1;return self.n
    def add(self,*row):self.clauses.append(list(row));assert self.n<100000 and len(self.clauses)<500000
    def one(self,vs):
        self.add(*vs)
        for i,v in enumerate(vs):
            for w in vs[i+1:]:self.add(-v,-w)
def fit(nodes,rot,S,seconds=3):
    C=CNF();N=[[[C.var() for _ in range(S)] for b in range(2)] for s in range(S)]
    O=[[C.var() for b in range(2)] for s in range(S)]
    X=[[C.var() for s in range(S)] for _ in nodes]
    for s in range(S):
        for b in range(2):C.one(N[s][b])
    C.add(X[0][0]);C.add(N[0][0][0]);C.add(-O[0][0])
    for i,(a,b) in enumerate(nodes):
        C.one(X[i]);ai=a&1;bi=b&1;j=rot[i]
        for s in range(S):
            C.add(-X[i][s],O[s][bi] if ai else -O[s][bi])
            for t in range(S):C.add(-X[i][s],-N[s][bi][t],X[j][t])
    path=ROOT/f'problem-{len(nodes)}-{S}.cnf'
    with path.open('w') as f:
        f.write(f'p cnf {C.n} {len(C.clauses)}\n')
        for row in C.clauses:f.write(' '.join(map(str,row))+' 0\n')
    try:
        run=subprocess.run([str(SOLVER),'-q',str(path)],capture_output=True,text=True,timeout=seconds)
        assert run.returncode in (10,20),run.stderr
        answer=run.returncode==10
    except subprocess.TimeoutExpired:answer=None
    result={'states':S,'answer':answer,'variables':C.n,'clauses':len(C.clauses)}
    if answer:
            model={int(v) for line in run.stdout.splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)>0}
            table=[[next(t for t in range(S) if N[s][b][t] in model) for b in range(2)] for s in range(S)]
            output=[[int(O[s][b] in model) for b in range(2)] for s in range(S)]
            assigned=[next(s for s in range(S) if row[s] in model) for row in X]
            for i,(a,b) in enumerate(nodes):
                assert output[assigned[i]][b&1]==a&1 and table[assigned[i]][b&1]==assigned[rot[i]]
            result.update(table=table,output=output,assignments=assigned)
    return result
def closure(table,output):
    # Exact finite-word inclusion, a sufficient stronger condition than merely
    # dyadic cyclic closure. Every initial source state / c bit is allowed.
    S=len(table);full=(1<<S)-1;todo=collections.deque();parent={}
    for astate in range(S):
        for c in range(2):
            v=(astate,c,full);parent[v]=None;todo.append(v)
    while todo:
        s,c,mask=todo.popleft()
        for b in range(2):
            if table[s][b] is None:continue
            a=output[s][b];nextc=c^(a|b);target=0
            for z in range(S):
                if (mask>>z)&1 and table[z][c] is not None and output[z][c]==b:target|=1<<table[z][c]
            nxt=(table[s][b],nextc,target)
            if nxt not in parent:
                parent[nxt]=((s,c,mask),(a,b,c));todo.append(nxt)
            if target==0:
                word=[];v=nxt
                while parent[v] is not None:v,letter=parent[v];word.append(letter)
                word.reverse()
                return {'passed':False,'counterexample':word,'explored':len(parent),'scope':'finite-word closure counterexample, not refutation of generic nonloss'}
    return {'passed':True,'explored':len(parent),'scope':'complete finite-word inclusion validator'}

def period_preserving(table,output):
    S=len(table);vertices=[(s,t,b) for s in range(S) for t in range(S) for b in range(2)]
    edges={v:[] for v in vertices}
    for s,t,last in vertices:
        for b in range(2):
            if table[s][b] is None or table[t][b] is None:continue
            edges[s,t,last].append(((table[s][b],table[t][b],b),output[s][b]!=output[t][b],b==last))
    counter=0;indices={};low={};stack=[];on=set();components=[]
    def visit(v):
        nonlocal counter
        indices[v]=low[v]=counter;counter+=1;stack.append(v);on.add(v)
        for w,_,_ in edges[v]:
            if w not in indices:visit(w);low[v]=min(low[v],low[w])
            elif w in on:low[v]=min(low[v],indices[w])
        if low[v]==indices[v]:
            comp=[]
            while True:
                w=stack.pop();on.remove(w);comp.append(w)
                if w==v:break
            components.append(set(comp))
    for v in vertices:
        if v not in indices:visit(v)
    for comp in components:
        inside=[(v,w,d,r) for v in comp for w,d,r in edges[v] if w in comp]
        if any(d for _,_,d,_ in inside) and any(r for _,_,_,r in inside):
            return {'passed':False,'reason':'nonalternating input supports distinct cyclic outputs','scc':sorted(comp)}
    for first in (0,1):
        for s in range(S):
            seen={};pairs=[];here=s
            while here not in seen:
                seen[here]=len(pairs);mid=table[here][first]
                if mid is None:break
                nxt=table[mid][1-first]
                if nxt is None:break
                pairs.append((output[here][first],output[mid][1-first]));here=nxt
            else:
                if len(set(pairs[seen[here]:]))>1:return {'passed':False,'reason':'alternating input has output period greater than two','first':first,'start':s}
    return {'passed':True,'product_vertices':len(vertices),'scope':'sufficient exact period-preservation test on all cyclic inputs'}

copy=fit([(0,0),(1,1)],[0,1],1);assert copy['answer'] is True
assert period_preserving(copy['table'],copy['output'])['passed']
bad=fit([(0,0),(1,0),(2,0)],[0,2,1],4);assert bad['answer'] is True
assert not period_preserving(bad['table'],bad['output'])['passed']
g=json.loads((ROOT/'PROFILE-GRAPH.json').read_text())['graphs'][-1]
nodes=[tuple(p) for p in g['nodes']];index={p:i for i,p in enumerate(nodes)};q=32
rotate=lambda w:(w>>1)|((w&1)<<(q-1))
rot=[index[(rotate(a),rotate(b))] for a,b in nodes]
results=[]
for S in (2,3,4,6,8):
    r=fit(nodes,rot,S)
    if r['answer']:
        used={(r['assignments'][i],b&1) for i,(a,b) in enumerate(nodes)}
        r['table']=[[t if (s,b) in used else None for b,t in enumerate(row)] for s,row in enumerate(r['table'])]
        r['period_preserving']=period_preserving(r['table'],r['output'])
        r['closure']=closure(r['table'],r['output'])
    results.append(r)
    print(json.dumps({k:v for k,v in r.items() if k!='assignments'}),flush=True)
    assert time.monotonic()-started<60
    if r['answer'] and r['period_preserving']['passed'] and r['closure']['passed']:break
out={'scope':'general partial cyclic decoder synthesis, not Lean proof','controls':{'copy_passed':True,'free_context_drop_rejected_by_validator':True},'results':results,'positive_profile_pairs':len(nodes),'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'solver_sha256':hashlib.sha256(SOLVER.read_bytes()).hexdigest()}
(ROOT/'RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
