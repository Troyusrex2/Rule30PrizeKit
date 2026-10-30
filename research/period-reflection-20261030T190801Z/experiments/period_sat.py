"""One preregistered falsification case and controls; no installations."""
from pathlib import Path
import itertools,subprocess,time,json,hashlib
R=Path(__file__).resolve().parent
solver='D:/MWB/Rule30/toolchain/lean-4.35.0-windows/bin/cadical.exe'
start=time.monotonic();results=[]
def run_case(name,P,N,control=False,pin=None,limit=5):
    clauses=[];vars=P*N
    def X(t,j):return (t%P)*N+j+1
    def rel(out,ins,f):
        for bits in itertools.product([False,True],repeat=len(ins)):
            wrong=not f(*bits)
            clauses.append([(-v if b else v) for v,b in zip(ins,bits)]+[-out if wrong else out])
    drives=[2,2,2,1,2,0,0,0]
    for t in range(P):
        if not control:clauses.append([X(t,0)])
        else:
            q=drives[t%8];rel(X(t+1,0),[X(t,0)],lambda a:a^(q!=0))
        rel(X(t+1,1),[X(t,1),X(t,0)],lambda a,b:a^(b or (control and drives[t%8]==2)))
        for j in range(2,N):rel(X(t+1,j),[X(t,j),X(t,j-1),X(t,j-2)],lambda a,b,c:a^(b or c))
    if not control:
        clauses += [[-X(0,1),X(0,2)],[X(0,1),-X(0,2)]]
    d=P//2
    for t in range(d):
        a,ap,b,bp=X(t,N-1),X(t+d,N-1),X(t,N-2),X(t+d,N-2)
        clauses += [[-a,ap],[a,-ap],[a,-b,bp],[a,b,-bp]]
    different=[]
    for j in range(N):
        vars+=1;different.append(vars);rel(vars,[X(0,j),X(d,j)],lambda a,b:a^b)
    clauses.append(different)
    if pin:
        for t,v in enumerate(pin):
            for j in range(N):clauses.append([X(t,j) if (v>>j)&1 else -X(t,j)])
    cnf=R/(name+'.cnf')
    with cnf.open('w',encoding='ascii',newline='\n') as f:
        f.write(f'p cnf {vars} {len(clauses)}\n')
        for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
    begin=time.monotonic();timed=False
    with (R/(name+'.log')).open('wb') as f:
        try:p=subprocess.run([solver,'-q','--seed=301030',str(cnf)],stdout=f,stderr=subprocess.STDOUT,timeout=limit)
        except subprocess.TimeoutExpired:timed=True;p=None
    out=dict(name=name,P=P,N=N,external_controls=control,vars=vars,clauses=len(clauses),seconds=time.monotonic()-begin,
        status='timeout' if timed else {10:'SAT',20:'UNSAT'}.get(p.returncode,'error'),cnf_sha256=hashlib.sha256(cnf.read_bytes()).hexdigest())
    if p is not None and p.returncode==10:
        text=(R/(name+'.log')).read_text(encoding='ascii');model={}
        for line in text.splitlines():
            if line.startswith('v '):
                for v in map(int,line[2:].split()):
                    if v:model[abs(v)]=v>0
        rows=[sum(int(model[X(t,j)])<<j for j in range(N)) for t in range(P)]
        mask=(1<<N)-1
        for t,x in enumerate(rows):
            if control:
                q=drives[t%8];c=int(q==2);h=int(q==1);actual=(x^(((x<<1)|c)|((x<<2)|(c<<1)|h)))&mask
            else:
                assert x&1;actual=(x^((x<<1)|(x<<2)))&mask
            assert actual==rows[(t+1)%P]
            y=rows[(t+d)%P];a=(x>>(N-1))&1;ap=(y>>(N-1))&1
            assert a==ap and (a or ((x>>(N-2))&1)==((y>>(N-2))&1))
        assert rows[0]!=rows[d]
        if not control:assert ((rows[0]>>1)&1)==((rows[0]>>2)&1)
        if pin:assert rows==pin
        out.update(independent_integer_model_verified=True,rows=rows)
    results.append(out)
    print(json.dumps({k:v for k,v in out.items() if k!='rows'}),flush=True)
    return out
known=[42,85,42,85,42,85,43,85,43,84,47,80,49,86,42,86]
assert run_case('positive_control',16,7,True,known,5)['status']=='SAT'
assert run_case('negative_control',8,8,False,None,5)['status']=='UNSAT'
run_case('source128_prefix32',128,32,False,None,45)
out=dict(results=results,total_seconds=time.monotonic()-start,
    scope='Finite falsification test only. No all-period result or kernel UNSAT certificate claimed. Windows CaDiCaL lacks a CPU timer; single-thread subprocess wall limits implement the stated caps.')
(R/'SAT_RESULT.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
