from pathlib import Path
from collections import deque
import json
r=Path(__file__).resolve().parent;d=json.loads((r/'single-flip-tail.json').read_bytes())
def profile(which,k):return d[which+'_prefix'][k] if k<8 else d['shared_tail'][(k-8)%4]
def bit(which,t,k):return (profile(which,k)>>(t%8))&1
def literal(row):return [(30>>((row[k]<<2)|(row[k+1]<<1)|row[k+2]))&1 for k in range(len(row)-2)]
checks=0;steps=128
for which in ('a','b'):
    row=[bit(which,0,k) for k in range(2*steps+32)]
    for t in range(steps+1):
        assert all(v==bit(which,t,k) for k,v in enumerate(row));checks+=len(row)
        if t<steps:row=literal(row)
assert [k for k in range(512) if bit('a',0,k)!=bit('b',0,k)]==[7]
for k in range(512):
    assert bit('a',0,k)==int(k>=5 and k%4==1)
    assert bit('b',0,k)==int((k>=5 and k%4==1) or k==7)
for t in range(128):
    assert bit('a',t,0)==bit('b',t,0) and bit('a',t,7)!=bit('b',t,7)
    assert (bit('a',t,1)|bit('a',t,2))==(bit('b',t,1)|bit('b',t,2))
assert bit('a',1,0)!=bit('a',3,0) and bit('a',5,1)!=bit('b',5,1)
old=[85,87,168,212,172,178,202,43]
def oldp(k):return old[k if k<4 else 4+(k-4)%4]
assert all(profile('a',k)==oldp(k+2) for k in range(64))
bad=d['shared_tail'].copy();bad[0]^=1
def badbit(t,k):return (((d['a_prefix'][k] if k<8 else bad[(k-8)%4]))>>(t%8))&1
assert any(badbit(t+1,k)!=((30>>((badbit(t,k)<<2)|(badbit(t,k+1)<<1)|badbit(t,k+2)))&1)
           for t in range(8) for k in range(12))
dfa=json.loads((r/'learned-reader.json').read_bytes())['dfa'];samples=[]
for T in [0,1,2,4,8,16,32,64,128,256,512,1024]:
    N=2*T+16;a=sum(int(k>=5 and k%4==1)<<k for k in range(N));b=a^(1<<7)
    q=0
    for k in reversed(range(N)):q=dfa['transitions'][q][(((a>>k)&1)<<1)|((b>>k)&1)]
    assert q==15;first=None;cap=max(4096,8*T+128)
    for t in range(cap):
        assert (a^b)>>7&1
        if (a^b)&1:first=t;break
        a^=(a>>1)|(a>>2);b^=(b>>1)|(b>>2)
    assert first is None or first>T
    samples.append({'delay':T,'width':N,'reader_state':q,'first_difference':first,
                    'cap':cap,'status':'different' if first is not None else 'unknown'})
# Independent truth-table check of every stored controlled-strip edge.
p=json.loads((r/'strip-observer.json').read_bytes());states=p['states'];edges=p['edges'];edge_checks=0
for i,st in enumerate(states):
    a,b,u,v=st
    for j,c,e in edges[i]:
        aa=[(a>>k)&1 for k in range(5)]+[u,v,c,e]
        bb=[(b>>k)&1 for k in range(5)]+[u,v,c,e]
        na=literal(aa);nb=literal(bb)
        expected=(sum(x<<k for k,x in enumerate(na[:5])),sum(x<<k for k,x in enumerate(nb[:5])),na[5],na[6])
        assert tuple(states[j])==expected and na[0]==nb[0];edge_checks+=1
def reachable(starts,graph):
    seen=set(starts);q=list(starts)
    for i in q:
        for j in graph[i]:
            if j not in seen:seen.add(j);q.append(j)
    return seen
g=[[j for j,_,_ in e] for e in edges];rev=[[] for _ in states]
for i,e in enumerate(g):
    for j in e:rev[j].append(i)
core=reachable(range(4),g)&reachable(range(4),rev)
assert len(core)==64
assert all(((states[i][0]^states[j][0])&1) for i in core for j in g[i] if j in core)
orbit=json.loads((r/'orbit-sections.json').read_bytes())
assert orbit['controls']==8239 and not orbit['closed'] and not orbit['infinite_signalizer_proved']
out={'passed':True,'literal_causal_cells_checked':checks,'single_flip_position':7,
     'known_precursor_spatial_shift':2,'corrupt_tail_rejected':True,'finite_samples':samples,
     'strip_edges_checked':edge_checks,'independently_recomputed_periodic_core_states':len(core),
     'periodic_core_head_flips_on_every_edge':True,'Lean_verified':False,
     'unbounded_eventual_separation_proved':False,'full_problem_solved':False}
(r/'independent-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
