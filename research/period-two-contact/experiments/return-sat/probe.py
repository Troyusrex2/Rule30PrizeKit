from pathlib import Path
import subprocess,json,time,hashlib,itertools
ROOT=Path(__file__).resolve().parent;started=time.monotonic();solver=Path.home()/'Rule30-offload/_cache/payload/toolchain/bin/cadical.exe';assert solver.exists()
def relation(c,a,b,d):return d==(c^(a|b))
table=[]
for vals in itertools.product((0,1),repeat=4):
    if not relation(*vals):table.append(tuple(-i if v else i for i,v in zip(range(1,5),vals)))
for vals in itertools.product((0,1),repeat=4):
    sat=all(any((vals[abs(v)-1]==1)==(v>0) for v in cl) for cl in table)
    literal=vals[3]==((30>>(4*vals[0]+2*vals[1]+vals[2]))&1)
    assert sat==literal
def make(W,Q,violation):
    v=lambda t,i:1+(t%Q)*W+i
    zero=Q*W+1;clauses=[[-zero],[v(0,0)]]
    for t in range(Q):
        for i in range(W):
            variables=[v(t,i),v(t,i-1) if i>=1 else zero,v(t,i-2) if i>=2 else zero,v(t+1,i)]
            for cl in table:clauses.append([variables[abs(x)-1]*(1 if x>0 else -1) for x in cl])
        a,b=v(t,W-1),v(t+1,W-1);clauses.extend([[a,b],[-a,-b]])
    if violation:
        a,b=v(0,W-2),v(2,W-2);clauses.extend([[a,b],[-a,-b]])
    return zero,clauses
def solve(W,Q,violation,label):
    n,clauses=make(W,Q,violation);path=ROOT/(label+'.cnf');path.write_text(f'p cnf {n} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
    tick=time.monotonic()
    try:r=subprocess.run([str(solver),'-q',str(path)],capture_output=True,text=True,timeout=2)
    except subprocess.TimeoutExpired:return {'width':W,'cycle':Q,'status':'UNKNOWN','seconds':time.monotonic()-tick}
    (ROOT/(label+'.solver.log')).write_text(r.stdout+r.stderr)
    assert r.returncode in (10,20),r.stderr
    result={'width':W,'cycle':Q,'status':'SAT' if r.returncode==10 else 'UNSAT','variables':n,'clauses':len(clauses),'seconds':time.monotonic()-tick}
    if r.returncode==10:
        assignments={abs(x):x>0 for line in r.stdout.splitlines() if line.startswith('v ') for x in map(int,line[2:].split()) if x}
        assert all(any(assignments[abs(x)]==(x>0) for x in cl) for cl in clauses)
        orbit=[sum(assignments[1+t*W+i]<<i for i in range(W)) for t in range(Q)]
        for t,w in enumerate(orbit):
            literal=sum(((30>>(4*((w>>i)&1)+2*((w>>(i-1))&1 if i>=1 else 0)+((w>>(i-2))&1 if i>=2 else 0)))&1)<<i for i in range(W))
            assert literal==orbit[(t+1)%Q]
            assert ((w>>(W-1))&1)!=((orbit[(t+1)%Q]>>(W-1))&1)
        assert orbit[0]&1
        if violation:assert ((orbit[0]>>(W-2))&1)!=((orbit[2]>>(W-2))&1)
        result.update({'seed':orbit[0],'orbit':orbit,'literal_replay_passed':True,'predecessor_violation_required':violation})
    return result
positive=solve(3,8,False,'control-positive');negative=solve(3,8,True,'control-negative')
assert positive['status']=='SAT' and positive['literal_replay_passed'] and negative['status']=='UNSAT'
results=[]
for W in range(25,33):
    r=solve(W,64,True,'width-'+str(W));results.append(r);print(json.dumps({k:v for k,v in r.items() if k!='orbit'}),flush=True)
    if r['status']!='UNSAT':break
out={'scope':'fixed SAT falsifier only; no general or Lean theorem','cnf_truth_table_controls':16,'positive_control':positive,'negative_control':negative,'results':results,'all_registered_cases_finished':len(results)==8,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seconds':time.monotonic()-started}
(ROOT/'RESULTS.json').write_bytes((json.dumps(out,indent=2)+'\n').encode());print(json.dumps({'scope':out['scope'],'cases':len(results),'seconds':out['seconds']}))
