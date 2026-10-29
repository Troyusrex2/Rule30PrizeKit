"""Independent, literal Boolean audit of fixed-clock graph certificates."""
from pathlib import Path
import json,time,hashlib
from collections import deque
ROOT=Path(__file__).resolve().parent
def bits(n,q):return [(n>>t)&1 for t in range(q)]
def least(xs):
    q=len(xs)
    for h in range(1,q+1):
        if q%h==0 and all(xs[t]==xs[(t+h)%q] for t in range(q)):return h
def verify(q):
    start=time.monotonic()
    p=ROOT/f'CLOCK-{q}-STATES.json';states={tuple(x) for x in json.loads(p.read_text())}
    assert (0,0) in states
    queue=deque([(0,0)]);seen={(0,0)};edges=0;period_cache={}
    def period(n):
        if n not in period_cache:period_cache[n]=least(bits(n,q))
        return period_cache[n]
    while queue:
        a,b=queue.popleft();av,bv=bits(a,q),bits(b,q)
        for head in [0,1]:
            cv=[head]
            for t in range(q):cv.append(cv[-1] ^ (av[t] or bv[t]))
            if cv[-1]!=cv[0]:continue
            c=sum(int(bit)<<t for t,bit in enumerate(cv[:-1]))
            assert all((cv[(t+1)%q] ^ cv[t]) == (av[t] or bv[t]) for t in range(q))
            assert (b,c) in states,(q,a,b,c)
            assert period(c)>=period(b),(q,a,b,c)
            edges+=1
            if (b,c) not in seen:seen.add((b,c));queue.append((b,c))
    assert seen==states
    return {'q':q,'all_states_reachable':True,'transition_closed':True,'all_columns_literal_recurrence_checked':True,'no_drop':True,'states':len(states),'edges':edges,'certificate_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'kernel_verified':False}
if __name__=='__main__':
    out=[]
    for q in [2,4,8,16,32,64]:
        out.append(verify(q));print(json.dumps(out[-1]),flush=True)
    (ROOT/'GRAPH-AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
