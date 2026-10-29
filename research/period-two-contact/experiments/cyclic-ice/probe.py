from pathlib import Path
import json,hashlib,itertools,subprocess,time
from dfa_validator import validate,period_two_dfa
ROOT=Path(__file__).resolve().parent;started=time.monotonic();solver=Path.home()/'Rule30-offload/_cache/payload/toolchain/bin/cadical.exe';assert solver.exists()
assert validate(period_two_dfa(),True)['passed'] and validate(period_two_dfa())['closure'] is not None
assert validate({'start':0,'delta':[[0]*4],'accept':[0]})['separation'] is not None
raw=(ROOT/'PROFILE-GRAPH.json').read_bytes();graphs=json.loads(raw)['graphs'];positive=set();negative=set();implications=set()
for g in graphs:
    q=g['q']
    if q>8:continue
    for a,b in g['nodes']:
        word=tuple(2*((a>>t)&1)+((b>>t)&1) for t in range(q))
        for k in range(q):positive.add(word[k:]+word[:k])
for q in (3,4):
    for word in itertools.product((1,2,3),repeat=q):
        if any((word[t]&1)!=(word[(t+2)%q]&1) for t in range(q)):negative.add(word)
class CNF:
    def __init__(self):self.n=0;self.clauses=[]
    def var(self):self.n+=1;return self.n
    def one(self,vs):
        self.clauses.append(vs)
        self.clauses.extend([[-a,-b] for i,a in enumerate(vs) for b in vs[i+1:]])
def encode(m):
    words=set(positive)|set(negative)
    for a,b in implications:words.add(a);words.add(b)
    prefixes={()}
    for w in words:
        for k in range(1,len(w)+1):prefixes.add(w[:k])
    assert len(prefixes)<=5000,'prefix_node_cap'
    prefixes=sorted(prefixes,key=lambda x:(len(x),x));index={p:i for i,p in enumerate(prefixes)}
    enc=CNF();delta=[[[enc.var() for j in range(m)] for a in range(4)] for i in range(m)];final=[enc.var() for i in range(m)];state=[[enc.var() for i in range(m)] for p in prefixes]
    for row in delta:
        for vs in row:enc.one(vs)
    for vs in state:enc.one(vs)
    enc.clauses.append([state[0][0]])
    for p in prefixes[1:]:
        parent=index[p[:-1]];child=index[p];symbol=p[-1]
        for i in range(m):
            for j in range(m):enc.clauses.append([-state[parent][i],-delta[i][symbol][j],state[child][j]])
    for w in positive:
        for i in range(m):enc.clauses.append([-state[index[w]][i],final[i]])
    for w in negative:
        for i in range(m):enc.clauses.append([-state[index[w]][i],-final[i]])
    for a,b in implications:
        for i in range(m):
            for j in range(m):enc.clauses.append([-state[index[a]][i],-state[index[b]][j],-final[i],final[j]])
    return enc,delta,final,len(prefixes)
history=[];found=None;stop=None
for m in (2,3,4):
    unsat=False
    for round in range(8):
        enc,delta,final,nodes=encode(m);label=f'm{m}-round{round}';path=ROOT/(label+'.cnf')
        path.write_text(f'p cnf {enc.n} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses))
        tick=time.monotonic()
        try:r=subprocess.run([str(solver),'-q',str(path)],capture_output=True,text=True,timeout=1)
        except subprocess.TimeoutExpired:
            stop='UNKNOWN';history.append({'states':m,'round':round,'status':stop,'seconds':time.monotonic()-tick});break
        assert r.returncode in (10,20),r.stderr
        entry={'states':m,'round':round,'status':'SAT' if r.returncode==10 else 'UNSAT','variables':enc.n,'clauses':len(enc.clauses),'prefix_nodes':nodes,'seconds':time.monotonic()-tick}
        if r.returncode==20:history.append(entry);unsat=True;break
        model={abs(v):v>0 for line in r.stdout.splitlines() if line.startswith('v ') for v in map(int,line[2:].split()) if v}
        assert all(any(model[abs(v)]==(v>0) for v in c) for c in enc.clauses)
        dfa={'start':0,'delta':[[next(j for j in range(m) if model[delta[i][a][j]]) for a in range(4)] for i in range(m)],'accept':[i for i in range(m) if model[final[i]]]}
        checked=validate(dfa);entry.update({'candidate':dfa,'validation':checked});history.append(entry)
        if checked['passed']:found=dfa;stop='candidate_not_kernel_verified';break
        if checked['root'] is not None:
            word=(0,)*checked['root']['length'];assert word not in positive;positive.add(word)
        if checked['closure'] is not None:
            triples=checked['closure']['letters'];incoming=tuple(2*a+b for a,b,c in triples);outgoing=tuple(2*b+c for a,b,c in triples)
            assert (incoming,outgoing) not in implications;implications.add((incoming,outgoing))
        if checked['separation'] is not None:
            word=tuple(2*a+b for a,b in checked['separation']['letters']);assert word not in negative;negative.add(word)
        assert time.monotonic()-started<60
    if stop is not None:break
    if not unsat:stop='iteration_cap';break
if stop is None:stop='registered_sizes_unsat'
out={'scope':'bounded ICE discovery and exact Python validator; no Lean certificate','stop':stop,'found_candidate':found,'history':history,'positive_words':len(positive),'negative_words':len(negative),'closure_implications':len(implications),'training_graph_sha256':hashlib.sha256(raw).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'validator_sha256':hashlib.sha256((ROOT/'dfa_validator.py').read_bytes()).hexdigest(),'seconds':time.monotonic()-started}
(ROOT/'RESULTS.json').write_bytes((json.dumps(out,indent=2)+'\n').encode())
print(json.dumps({k:v for k,v in out.items() if k not in ['history','found_candidate']}));print(json.dumps({'iterations':len(history),'candidate_found':found is not None,'last':{k:v for k,v in history[-1].items() if k not in ['candidate','validation']}}))
