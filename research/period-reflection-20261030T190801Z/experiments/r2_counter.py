from pathlib import Path
import itertools,subprocess,time,json
R=Path(__file__).resolve().parent;N=10;P=16;Q=8;clauses=[]
def X(t,j):return (t%P)*N+j+1
def V(t,j):return P*N+(t%Q)*4+j+1
def rel(out,ins,f):
    for b in itertools.product([False,True],repeat=len(ins)):
        wrong=not f(*b);clauses.append([(-v if bit else v) for v,bit in zip(ins,b)]+[-out if wrong else out])
for t in range(P):
    rel(X(t+1,0),[X(t,0),V(t,0),V(t,1)],lambda a,b,c:a^(b or c))
    rel(X(t+1,1),[X(t,1),X(t,0),V(t,0)],lambda a,b,c:a^(b or c))
    for j in range(2,N):rel(X(t+1,j),[X(t,j),X(t,j-1),X(t,j-2)],lambda a,b,c:a^(b or c))
    for j in [N-2,N-1]:clauses += [[X(t,j),-X(t+Q,j)],[-X(t,j),X(t+Q,j)]]
for t in range(Q):
    rel(V(t+1,0),[V(t,0),V(t,1),V(t,2)],lambda a,b,c:a^(b or c))
    rel(V(t+1,1),[V(t,1),V(t,2),V(t,3)],lambda a,b,c:a^(b or c))
clauses += [[-X(0,0)],[X(Q,0)],[V(0,0)]]
cnf=R/'r2_counter.cnf'
with cnf.open('w',encoding='ascii',newline='\n') as f:
    f.write(f'p cnf {P*N+Q*4} {len(clauses)}\n')
    for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
start=time.monotonic()
try:
    with (R/'r2_counter.log').open('wb') as f:
        p=subprocess.run(['D:/MWB/Rule30/toolchain/lean-4.35.0-windows/bin/cadical.exe','-q',str(cnf)],stdout=f,stderr=subprocess.STDOUT,timeout=10)
    status={10:'SAT',20:'UNSAT'}.get(p.returncode,'error')
except subprocess.TimeoutExpired:status='timeout'
out=dict(status=status,seconds=time.monotonic()-start,N=N,period=16,external_period=8)
if status=='SAT':
    model={}
    for line in (R/'r2_counter.log').read_text(encoding='ascii').splitlines():
        if line.startswith('v '):
            for i in map(int,line[2:].split()):
                if i:model[abs(i)]=i>0
    rows=[sum(model[X(t,j)]<<j for j in range(N)) for t in range(P)]
    controls=[[int(model[V(t,j)]) for j in range(4)] for t in range(Q)]
    for t,x in enumerate(rows):
        c,h,g,f=controls[t%Q];actual=(x^(((x<<1)|c)|((x<<2)|(c<<1)|h)))&((1<<N)-1)
        assert actual==rows[(t+1)%P]
        assert x>>(N-2)==rows[(t+Q)%P]>>(N-2)
    for t,(c,h,g,f) in enumerate(controls):
        assert controls[(t+1)%Q][0]==c^(h|g)
        assert controls[(t+1)%Q][1]==h^(g|f)
    assert rows[0]&1==0 and rows[Q]&1==1 and controls[0][0]==1
    word=['C' if c else ('B' if h else 'A') for c,h,_,_ in controls]
    assert all(''.join((word*2)[t:t+3])!='ACC' for t in range(Q))
    out.update(rows=rows,controls=controls,chronological_word=''.join(word),independent_integer_model_verified=True)
out['scope']='Synthetic two-ancestor relaxation only; no actual black-edge source or prize counterexample.'
(R/'R2_COUNTER.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(out))
