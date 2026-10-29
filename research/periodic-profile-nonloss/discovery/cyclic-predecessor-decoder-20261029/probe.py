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
    A=[[[C.var() for _ in range(S)] for b in range(2)] for s in range(S)]
    R1=[C.var() for _ in range(S)];C.one(R1)
    for s in range(S):
        for b in range(2):C.one(N[s][b]);C.one(A[s][b])
    C.add(X[0][0]);C.add(N[0][0][0]);C.add(-O[0][0])
    for i,(a,b) in enumerate(nodes):
        C.one(X[i]);ai=a&1;bi=b&1;j=rot[i]
        for s in range(S):
            C.add(-X[i][s],O[s][bi] if ai else -O[s][bi])
            for t in range(S):C.add(-X[i][s],-N[s][bi][t],X[j][t])
    for s in range(S):
        for t in range(S):
            C.add(-N[s][0][t],N[t][0][0]) # 00 resets to state0
            for u in range(S):
                C.add(-N[s][1][t],-N[t][1][u],R1[u]) # 11 resets
                for b in range(2):
                    C.add(-N[s][b][t],-N[t][1-b][u],A[s][b][u])
                    C.add(-A[s][b][t],-A[t][b][u],A[s][b][u]) # (01)^2=01 and (10)^2=10
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
            assert len({table[table[s][0]][0] for s in range(S)})==1
            assert len({table[table[s][1]][1] for s in range(S)})==1
            for s in range(S):
                for b in range(2):
                    t=table[table[s][b]][1-b]
                    assert table[table[t][b]][1-b]==t
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
            a=output[s][b];nextc=c^(a|b);target=0
            for z in range(S):
                if (mask>>z)&1 and output[z][c]==b:target|=1<<table[z][c]
            nxt=(table[s][b],nextc,target)
            if nxt not in parent:
                parent[nxt]=((s,c,mask),(a,b,c));todo.append(nxt)
            if target==0:
                word=[];v=nxt
                while parent[v] is not None:v,letter=parent[v];word.append(letter)
                word.reverse()
                return {'passed':False,'counterexample':word,'explored':len(parent),'scope':'finite-word closure counterexample, not refutation of generic nonloss'}
    return {'passed':True,'explored':len(parent),'scope':'complete finite-word inclusion validator'}
copy=fit([(0,0),(1,1)],[0,1],1);assert copy['answer'] is True
bad=fit([(0,0),(1,0),(2,0)],[0,2,1],4);assert bad['answer'] is False
g=json.loads((ROOT/'PROFILE-GRAPH.json').read_text())['graphs'][-1];assert g['q']==32 and len(g['nodes'])==2116
nodes=[tuple(p) for p in g['nodes']];index={p:i for i,p in enumerate(nodes)};q=32;mask=(1<<q)-1
rotate=lambda w:(w>>1)|((w&1)<<(q-1))
rot=[index[(rotate(a),rotate(b))] for a,b in nodes]
results=[]
for S in (2,3,4,6,8):
    r=fit(nodes,rot,S)
    if r['answer']:r['closure']=closure(r['table'],r['output'])
    results.append(r)
    print(json.dumps({k:v for k,v in r.items() if k!='assignments'}),flush=True)
    assert time.monotonic()-started<60
    if r['answer'] and r['closure']['passed']:break
out={'scope':'decoder synthesis and exact finite checks; not a Lean proof','controls':{'copy':copy,'free_context_drop_rejected':bad},'results':results,'positive_profile_pairs':len(nodes),'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'solver_sha256':hashlib.sha256(SOLVER.read_bytes()).hexdigest()}
(ROOT/'RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
