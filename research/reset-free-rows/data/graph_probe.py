from pathlib import Path
from array import array
from collections import deque,Counter
import itertools,json,time,hashlib
ROOT=Path(__file__).resolve().parent
ATOMS=[(0,0,0),(1,0,0),(0,1,1),(1,1,0),(1,1,1),(1,1,2)]
INDEX={a:i for i,a in enumerate(ATOMS)}
def build(H):
    count=6**H;nexts=[array('i',[-1])*count,array('i',[-1])*count];reverse=[[] for _ in range(count)];indegree=array('i',[0])*count;outdegree=array('i',[0])*count
    for state in range(count):
        digits=[];v=state
        for t in range(H):digits.append(v%6);v//=6
        atoms=[ATOMS[d] for d in digits]
        for top in (0,1):
            target=0;place=1
            for t,(p,c,r) in enumerate(atoms):
                bit=top if t==H-1 else atoms[t+1][1]^(c|p)
                if not bit and r==1:break
                rnext=(r+1)%3 if bit else 0
                target+=INDEX[c,bit,rnext]*place;place*=6
            else:
                nexts[top][state]=target;reverse[target].append(state);indegree[target]+=1;outdegree[state]+=1
    alive=bytearray(b'\1')*count;q=deque(i for i in range(count) if not indegree[i] or not outdegree[i])
    while q:
        v=q.popleft()
        if not alive[v]:continue
        alive[v]=0
        for targets in nexts:
            w=targets[v]
            if w>=0 and alive[w]:
                indegree[w]-=1
                if not indegree[w]:q.append(w)
        for w in reverse[v]:
            if alive[w]:
                outdegree[w]-=1
                if not outdegree[w]:q.append(w)
    vertices=[i for i in range(count) if alive[i]];seen=bytearray(count);order=[]
    for root in vertices:
        if seen[root]:continue
        seen[root]=1;stack=[(root,0)]
        while stack:
            v,j=stack[-1]
            if j==2:order.append(v);stack.pop();continue
            stack[-1]=(v,j+1);w=nexts[j][v]
            if w>=0 and alive[w] and not seen[w]:seen[w]=1;stack.append((w,0))
    component=array('i',[-1])*count;components=[]
    for root in reversed(order):
        if component[root]>=0:continue
        cid=len(components);members=[];stack=[root];component[root]=cid
        while stack:
            v=stack.pop();members.append(v)
            for w in reverse[v]:
                if alive[w] and component[w]<0:component[w]=cid;stack.append(w)
        components.append(members)
    connections=[];descriptions=[]
    for cid,vs in enumerate(components):
        internal=[sum(w>=0 and alive[w] and component[w]==cid for w in [nexts[0][v],nexts[1][v]]) for v in vs]
        simple=all(n==1 for n in internal)
        for v in vs:
            for targets in nexts:
                w=targets[v]
                if w>=0 and alive[w] and component[w]!=cid:connections.append([cid,component[w]])
        cycle=[];words=[]
        if simple:
            at=vs[0]
            while at not in cycle:
                cycle.append(at);at=next(w for w in [nexts[0][at],nexts[1][at]] if w>=0 and alive[w] and component[w]==cid)
            assert len(cycle)==len(vs)
            for t in range(H):words.append(''.join(str(ATOMS[(v//(6**t))%6][1]) for v in cycle))
        descriptions.append({'size':len(vs),'simple_cycle':simple,'row_words':words,'states':vs if len(vs)<=100 else None})
    return {'height':H,'all_states':count,'essential_states':len(vertices),'essential_edges':sum(outdegree[v] for v in vertices),'components':descriptions,'inter_component_edges':connections},nexts,alive

def run_free(w,p):
    if w==(1<<p)-1:return True
    zero=next(k for k in range(p) if not(w>>k)&1);n=0
    for k in range(1,p+1):
        if(w>>((zero+k)%p))&1:n+=1
        else:
            if n%3==1:return False
            n=0
    return True
def evolve(w,p):
    return sum(((30>>(4*((w>>((k+1)%p))&1)+2*((w>>k)&1)+((w>>((k-1)%p))&1)))&1)<<k for k in range(p))
def cyclic_graph_accept(rows,p,H,nexts):
    # Enumerate scanner phases only for constant-one rows, otherwise runs fix them.
    choices=[]
    for w in rows:
        if w==(1<<p)-1:choices.append(list(range(3)))
        else:choices.append([None])
    for phases in itertools.product(*choices):
        mods=[]
        for w,phase in zip(rows,phases):
            if phase is not None:mods.append([(phase+k)%3 for k in range(p)])
            else:
                r=[]
                for k in range(p):
                    n=0
                    while (w>>((k-n)%p))&1:n+=1
                    r.append(n%3)
                mods.append(r)
        states=[];valid=True
        for k in range(p):
            state=0
            for t,w in enumerate(rows):
                atom=((w>>((k-1)%p))&1,(w>>k)&1,mods[t][k])
                if atom not in INDEX:valid=False;break
                state+=INDEX[atom]*(6**t)
            if not valid:break
            states.append(state)
        if valid and all(states[(k+1)%p] in (nexts[0][states[k]],nexts[1][states[k]]) for k in range(p)):return True
    return False
def main():
    started=time.monotonic();results=[];previous=None;stable=0
    for H in range(1,8):
        r,nexts,alive=build(H)
        if H<=4:
            tested=0
            for p in range(1,11):
                # Repeat each cyclic row three times to accommodate the scanner's
                # artificial mod3 phase on constant-one rows.
                for w in range(1<<p):
                    words=[w]
                    for t in range(H-1):words.append(evolve(words[-1],p))
                    expected=all(run_free(v,p) for v in words)
                    copies=[v|(v<<p)|(v<<(2*p)) for v in words]
                    actual=cyclic_graph_accept(copies,3*p,H,nexts)
                    assert actual==expected,(H,p,w,expected,actual)
                    tested+=1
            r['literal_cyclic_controls']=tested
        r['seconds']=time.monotonic()-started;results.append(r)
        (ROOT/'RESULTS.json').write_text(json.dumps({'results':results,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'kernel_verified':False},indent=2)+'\n')
        print(json.dumps({k:v for k,v in r.items() if k!='components'}),flush=True)
        signature=(r['essential_states'],r['essential_edges'],sorted((v['size'],v['simple_cycle']) for v in r['components']),len(r['inter_component_edges']))
        if signature==previous:stable+=1
        else:stable=0
        if stable>=1:break
        previous=signature
if __name__=='__main__':main()
