from pathlib import Path
from itertools import product
import json,time,collections
ROOT=Path(__file__).resolve().parent

def ring_mul(a,b,poly):
    c=0
    while b:
        if b&1:c^=a
        a<<=1;b>>=1
    degree=poly.bit_length()-1
    for k in range(c.bit_length()-1,degree-1,-1):
        if (c>>k)&1:c^=poly<<(k-degree)
    return c

def group(degree,poly):
    q=1<<degree;rm=[[ring_mul(a,b,poly) for b in range(q)] for a in range(q)]
    elems=[a for a in product(range(q),repeat=4) if rm[a[0]][a[3]]^rm[a[1]][a[2]]==1]
    index={a:i for i,a in enumerate(elems)};identity=index[(1,0,0,1)]
    def matrix_mul(a,b):
        return (rm[a[0]][b[0]]^rm[a[1]][b[2]],rm[a[0]][b[1]]^rm[a[1]][b[3]],
                rm[a[2]][b[0]]^rm[a[3]][b[2]],rm[a[2]][b[1]]^rm[a[3]][b[3]])
    mul=[[index[matrix_mul(a,b)] for b in elems] for a in elems]
    inv=[next(j for j in range(len(elems)) if mul[i][j]==identity and mul[j][i]==identity) for i in range(len(elems))]
    masks=[[0]*len(elems) for _ in elems]
    for u in range(len(elems)):
        for v in range(len(elems)):
            masks[u][v]=sum(1<<m for m in range(len(elems)) if mul[u][m]==mul[m][v])
    return elems,identity,mul,inv,masks

def image(word,w,rule=30):
    return sum(((rule>>(4*((word>>j)&1)+2*((word>>(j+1))&1)+((word>>(j+2))&1)))&1)<<j for j in range(w))

def structure(w,rule=30):
    nv=1<<(w-1);vm=nv-1;tree=set();seen={0};queue=collections.deque([0])
    incident=[[] for _ in range(nv)]
    for edge in range(1<<w):
        a=edge&vm;b=edge>>1;incident[a].append((edge,b));incident[b].append((edge,a))
    while queue:
        v=queue.popleft()
        for edge,t in incident[v]:
            if t not in seen:seen.add(t);queue.append(t);tree.add(edge)
    assert len(tree)==nv-1
    fixed=tree|{0}
    if image((1<<(w+2))-1,w,rule)==0:fixed.add((1<<w)-1)
    free=[e for e in range(1<<w) if e not in fixed]
    nt=1<<(w+1);tm=nt-1;edges=[];order=[];seen={0};queue=collections.deque([0]);path=[];checks=[]
    while queue:
        v=queue.popleft();order.append(v)
        for b in range(2):
            word=v|(b<<(w+1));target=word>>1
            edge=(v,target,image(word,w,rule),(word>>1)&((1<<w)-1),word)
            edges.append(edge)
            if target not in seen:
                seen.add(target);queue.append(target);path.append(edge)
            else:checks.append(edge)
    assert len(order)==nt and len(edges)==2*nt and len(path)==nt-1
    return sorted(tree),free,nt,path,checks,edges

def recover(L,root,identity,mul,inv,nt,path,edges):
    M=[None]*nt;M[0]=root
    for u,v,ly,lo,_ in path:M[v]=mul[mul[L[ly]][M[u]]][inv[L[lo]]]
    assert all(m is not None for m in M)
    assert all(mul[L[ly]][M[u]]==mul[M[v]][L[lo]] for u,v,ly,lo,_ in edges)
    return M

def search(name,w,g,cap,rule=30):
    elems,identity,mul,inv,masks=g;size=len(elems)
    tree,free,nt,path,checks,edges=structure(w,rule);L=[identity]*(1<<w)
    start=time.monotonic();examined=0;total=size**len(free);answers=[]
    for values in product(range(size),repeat=len(free)):
        if examined%1024==0 and time.monotonic()-start>cap:
            return {'group':name,'width':w,'status':'timeout_partial','examined':examined,'total':total,'seconds':time.monotonic()-start,'solutions':answers}
        examined+=1
        if all(v==identity for v in values):continue
        for e,v in zip(free,values):L[e]=v
        A=[identity]*nt;B=[identity]*nt
        for u,v,ly,lo,_ in path:
            A[v]=mul[L[ly]][A[u]];B[v]=mul[B[u]][inv[L[lo]]]
        allowed=(1<<size)-1
        for u,v,ly,lo,_ in checks:
            U=mul[mul[inv[A[v]]][L[ly]]][A[u]]
            V=mul[mul[B[v]][L[lo]]][inv[B[u]]]
            allowed&=masks[U][V]
            if not allowed:break
        if allowed:
            root=(allowed&-allowed).bit_length()-1
            M=recover(L,root,identity,mul,inv,nt,path,edges)
            answers.append({'L':L.copy(),'M':M,'root':root})
            # A positive is investigated rather than turning this into a census.
            return {'group':name,'width':w,'status':'nontrivial_candidate','examined':examined,'total':total,'seconds':time.monotonic()-start,'solutions':answers}
    return {'group':name,'width':w,'status':'no_nongauge_cocycle_in_registered_class','examined':examined,'total':total,
            'seconds':time.monotonic()-start,'free_edges':free,'gauge_tree':tree,'solutions':answers}

def main():
    stages=[('SL2_F2',1,0b10,[2,3,4]),('SL2_dual_F2',2,0b100,[2,3]),('SL2_F4',2,0b111,[2,3])]
    results=[]
    for name,d,p,widths in stages:
        g=group(d,p)
        (ROOT/(name+'-group.json')).write_text(json.dumps({'elements':g[0],'identity':g[1],'mul':g[2],'inv':g[3]},indent=2)+'\n')
        for w in widths:
            r=search(name,w,g,45);results.append(r)
            (ROOT/'monodromy-results.json').write_text(json.dumps(results,indent=2)+'\n')
            print(name,'width',w,r['status'],'examined',r['examined'],'of',r['total'],'seconds',round(r['seconds'],3),flush=True)
            if r['solutions']:return

if __name__=='__main__':main()
