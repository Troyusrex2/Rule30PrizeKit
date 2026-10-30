from pathlib import Path
from itertools import product
import collections,time,json
from monodromy_probe import group,structure,recover
ROOT=Path(__file__).resolve().parent
def classes(g):
    elems,e,mul,inv,_=g;seen=set();out=[]
    for a in range(len(elems)):
        if a in seen:continue
        cls=sorted({mul[mul[h][a]][inv[h]] for h in range(len(elems))})
        seen.update(cls);out.append((a,cls))
    return out
def power(a,k,e,mul,inv):
    if k<0:return power(inv[a],-k,e,mul,inv)
    q=e
    for _ in range(k):q=mul[q][a]
    return q
def baseline(w,a,g,tree):
    _,e,mul,inv,_=g;nv=1<<(w-1);mask=nv-1
    adj=[[] for _ in range(nv)]
    for edge in tree:
        u=edge&mask;v=edge>>1;adj[u].append((v,-1));adj[v].append((u,1))
    height={0:0};q=collections.deque([0])
    while q:
        u=q.popleft()
        for v,delta in adj[u]:
            if v not in height:height[v]=height[u]+delta;q.append(v)
    return [power(a,height[edge>>1]+1-height[edge&mask],e,mul,inv) for edge in range(1<<w)]
def search(name,w,g,cap=45):
    elems,e,mul,inv,masks=g;size=len(elems);tree,free,nt,path,checks,edges=structure(w)
    # structure() already fixed zero and allones for Rule30; free are the rest.
    start=time.monotonic();examined=0
    for a,cls in classes(g):
        base=baseline(w,a,g,tree)
        for last in cls:
            for values in product(range(size),repeat=len(free)):
                if examined%1024==0 and time.monotonic()-start>cap:
                    return {'group':name,'width':w,'status':'timeout_partial','examined':examined,'seconds':time.monotonic()-start}
                examined+=1;L=[e]*(1<<w);L[0]=a;L[-1]=last
                for edge,v in zip(free,values):L[edge]=v
                if L==base:continue
                A=[e]*nt;B=[e]*nt
                for u,v,ly,lo,_ in path:A[v]=mul[L[ly]][A[u]];B[v]=mul[B[u]][inv[L[lo]]]
                allowed=(1<<size)-1
                for u,v,ly,lo,_ in checks:
                    U=mul[mul[inv[A[v]]][L[ly]]][A[u]];V=mul[mul[B[v]][L[lo]]][inv[B[u]]]
                    allowed&=masks[U][V]
                    if not allowed:break
                if allowed:
                    root=(allowed&-allowed).bit_length()-1;M=recover(L,root,e,mul,inv,nt,path,edges)
                    return {'group':name,'width':w,'status':'nonbackground_candidate','examined':examined,'seconds':time.monotonic()-start,
                            'vacuum':a,'L':L,'M':M,'root':root,'background_connection':base}
    return {'group':name,'width':w,'status':'no_nonbackground_cocycle_in_registered_class','examined':examined,'seconds':time.monotonic()-start}
def main():
    results=[]
    for name,d,p,widths in [('SL2_F2',1,2,[1,2,3]),('SL2_dual_F2',2,4,[1,2]),('SL2_F4',2,7,[1,2])]:
        g=group(d,p)
        for w in widths:
            r=search(name,w,g);results.append(r)
            (ROOT/'vacuum-twist-results.json').write_text(json.dumps(results,indent=2)+'\n')
            print(name,w,r['status'],'examined',r['examined'],'seconds',round(r['seconds'],3),flush=True)
            if r['status']=='nonbackground_candidate':return
if __name__=='__main__':main()
