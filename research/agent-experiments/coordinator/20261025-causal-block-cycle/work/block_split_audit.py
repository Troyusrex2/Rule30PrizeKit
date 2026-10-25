"""Test a precise translation-invariant reading of the proposed block ordinal.
Blocks are maximal runs of disagreement cells. This is a diagnostic experiment,
not a claim that it covers every notion of a non-regular block or ordinal.
"""
from pathlib import Path
import hashlib,json,time
root=Path(__file__).resolve().parent;started=time.monotonic()
def phi(a):return a^((a<<1)|(a<<2))
def runs(d):
    out=[]
    while d:
        lo=(d&-d).bit_length()-1
        n=((d>>lo)^((d>>lo)+1)).bit_length()-1
        out.append((lo,lo+n-1));d &= ~(((1<<n)-1)<<lo)
    return out
def desc(a,b,interval,halo,phase):
    lo,hi=interval
    word=tuple(((a>>i)&1)|(((b>>i)&1)<<1) if i>=0 else 0 for i in range(lo-halo,hi+halo+1))
    return (phase,word)
def physical(s):
    return {x for x in range(min(s|{0})-1,max(s|{0})+2) if int(x-1 in s)^(int(x in s)|int(x+1 in s))}

# Independent physical-coordinate oracle for the packed evolution and runs.
rows=[1];sets=[{0}]
for t in range(1,320):
    rows.append(phi(rows[-1]));sets.append(physical(sets[-1]))
    assert rows[-1]==sum(1<<(t-x) for x in sets[-1])
checks=0
for T,P in [(0,1),(0,16),(7,16),(16,3)]:
    for t in range(12):
        a=rows[T+t]<<P;b=rows[T+P+t];frame=T+P+t;d=a^b
        intervals=runs(d);assert sum(((1<<(hi-lo+1))-1)<<lo for lo,hi in intervals)==d
        assert {frame-i for lo,hi in intervals for i in range(lo,hi+1)}==sets[T+t]^sets[T+P+t]
        checks+=1

halos=[0,1,2,4,8];graphs={h:{} for h in halos};edge_witness={h:{} for h in halos}
split_count=0;guarded=0;merges=[];literal=None
for P in [16,1,2,3,4,7,8,32]:
    for T in range(32):
        a=rows[T]<<P;b=rows[T+P]
        for t in range(128):
            an=phi(phi(a));bn=phi(phi(b));old=runs(a^b);new=runs(an^bn)
            frame=T+P+t
            guard=all(((rows[T+t+i]>>(T+t+i))&1)==((rows[T+P+t+i]>>(T+P+t+i))&1) for i in range(3))
            parentsets=[tuple(k for k,(lo,hi) in enumerate(old) if lo<=nh and nl-4<=hi) for nl,nh in new]
            for k,parent in enumerate(old):
                children=[j for j,ps in enumerate(parentsets) if ps==(k,)]
                if len(children)<2:continue
                split_count+=1
                if not guard:continue
                guarded+=1
                witness={'T':T,'P':P,'time':t,'step':2,'frame':frame,'parent':list(parent),
                         'children':[list(new[j]) for j in children],
                         'initial_current_A_hex':hex(a),'initial_current_B_hex':hex(b),
                         'next_A_hex':hex(an),'next_B_hex':hex(bn),'center_guard':True}
                for h in halos:
                    u=desc(a,b,parent,h,(T+t)%16)
                    for j in children:
                        v=desc(an,bn,new[j],h,(T+t+2)%16)
                        graphs[h].setdefault(u,set()).add(v);edge_witness[h].setdefault((u,v),witness)
                        if literal is None and h==0 and u[1]==v[1]:literal=witness
            if guard and len(merges)<4:
                for j,ps in enumerate(parentsets):
                    if len(ps)>1:
                        merges.append({'T':T,'P':P,'time':t,'parents':[list(old[k]) for k in ps],'child':list(new[j])});break
            a,b=phi(a),phi(b)

def find_cycle(graph):
    color={};path=[];place={}
    def visit(u):
        color[u]=1;place[u]=len(path);path.append(u)
        for v in graph.get(u,[]):
            if color.get(v)==1:return path[place[v]:]+[v]
            if color.get(v,0)==0:
                found=visit(v)
                if found:return found
        path.pop();place.pop(u);color[u]=2
    for u in graph:
        if color.get(u,0)==0:
            found=visit(u)
            if found:return found
    return None
results=[]
for h,g in graphs.items():
    cycle=find_cycle(g);result={'halo':h,'nodes_with_children':len(g),'edges':sum(map(len,g.values())),'strict_cycle_found':cycle is not None}
    if cycle:
        result['cycle']=[{'phase':u[0],'word':list(u[1])} for u in cycle]
        result['witnesses']=[edge_witness[h][(u,v)] for u,v in zip(cycle,cycle[1:])]
    results.append(result)
out={'finite_only':True,'Lean_verified':False,'independent_physical_rows':319,'block_oracle_cases':checks,
     'split_count':split_count,'guarded_split_count':guarded,'first_literal_child_copy':literal,
     'strict_order_graphs':results,'merge_examples':merges,'seconds':time.monotonic()-started,
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'Only maximal contiguous disagreement blocks, paired-cell word with fixed halo, translation-invariant ordinal indexed by phase mod16; every split child is required strictly smaller after a guarded two-step. A directed strict cycle excludes such an order but not position-dependent, history-dependent, differently segmented or more selective ranks.'}
(root/'block-split-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'splits':split_count,'guarded_splits':guarded,'cycle_results':[{k:v for k,v in r.items() if k not in ['cycle','witnesses']} for r in results],'first_literal_copy':literal,'seconds':out['seconds']}),flush=True)
