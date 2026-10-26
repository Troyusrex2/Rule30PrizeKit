"""Exact finite-width trace partition via permutation orbits and primitive necklaces.
Hashes only select collision chains. Every candidate match is compared exactly.
No finite enumeration is claimed to prove unbounded reader completeness.
"""
from pathlib import Path
import json,time
import numpy as np
from numba import njit,types
from numba.typed import Dict
r=Path(__file__).resolve().parent
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa']
T=np.array(reader['transitions'],dtype=np.int16);A=np.zeros(17,dtype=np.uint8)
for q in reader['accepting']:A[q]=1
key_type=types.UniTuple(types.uint64,2)
@njit(cache=False)
def booth(bits,p):
    i=0;j=1;k=0
    while i<p and j<p and k<p:
        a=bits[(i+k)%p];b=bits[(j+k)%p]
        if a==b:k+=1
        elif a>b:
            i=i+k+1
            if i<=j:i=j+1
            k=0
        else:
            j=j+k+1
            if j<=i:j=i+1
            k=0
    return min(i,j)%p
@njit(cache=False)
def partition(width,T,A,save_reps):
    N=1<<width;mask=N-1;cap=1<<((2*width-1)//3)
    visited=np.zeros(N,dtype=np.uint8)
    initial_capacity=min(N,65536)
    offsets=np.empty(initial_capacity,dtype=np.uint32);lengths=np.empty(initial_capacity,dtype=np.uint32)
    links=np.empty(initial_capacity,dtype=np.int32);store=np.empty(initial_capacity,dtype=np.uint8)
    reps=np.empty(initial_capacity,dtype=np.uint32)
    bystate=np.empty(N if save_reps else 0,dtype=np.uint32)
    orbit=np.empty(cap,dtype=np.uint32);bits=np.empty(cap,dtype=np.uint8)
    lookup=Dict.empty(key_type=key_type,value_type=types.int64)
    classes=0;space=0;cycles=0;seen=0;reader_checks=0;exact_matches=0;collisions=0;losses=0;max_orbit=0
    for initial in range(N):
        if visited[initial]:continue
        cur=initial;L=0
        while not visited[cur]:
            if L>=cap:raise RuntimeError('proved clock cap exceeded')
            visited[cur]=1;seen+=1;orbit[L]=cur;bits[L]=(cur>>(width-1))&1;L+=1
            cur=(cur^((cur<<1)|(cur<<2)))&mask
        if cur!=initial:raise RuntimeError('orbit merged despite invertibility')
        if L&(L-1):raise RuntimeError('non-dyadic orbit length')
        cycles+=1;max_orbit=max(max_orbit,L);p=L
        while p>1:
            half=p//2;equal=True
            for i in range(half):
                if bits[i]!=bits[i+half]:equal=False;break
            if not equal:break
            p=half
        if p<L:losses+=1
        rot=booth(bits,p);h=np.uint64(1469598103934665603)
        for i in range(p):h=(h^np.uint64(bits[(rot+i)%p]+1))*np.uint64(1099511628211)
        key=(np.uint64(p),h);head=np.int64(-1)
        if key in lookup:head=lookup[key]
        cid=head;matched=-1
        while cid!=-1:
            equal=True;off=int(offsets[cid])
            for i in range(p):
                if store[off+i]!=bits[(rot+i)%p]:equal=False;break
            if equal:matched=cid;exact_matches+=1;break
            collisions+=1;cid=int(links[cid])
        if matched==-1:
            if space+p>N:raise RuntimeError('canonical storage accounting failed')
            if classes==len(offsets):
                newoff=np.empty(2*len(offsets),dtype=np.uint32);newoff[:classes]=offsets
                newlen=np.empty(2*len(lengths),dtype=np.uint32);newlen[:classes]=lengths
                newlink=np.empty(2*len(links),dtype=np.int32);newlink[:classes]=links
                offsets=newoff;lengths=newlen;links=newlink
            if space+p>len(store):
                size=len(store)
                while size<space+p:size=min(N,2*size)
                newstore=np.empty(size,dtype=np.uint8);newstore[:space]=store[:space]
                newreps=np.empty(size,dtype=np.uint32);newreps[:space]=reps[:space]
                store=newstore;reps=newreps
            cid=classes;classes+=1;offsets[cid]=space;lengths[cid]=p;links[cid]=head;lookup[key]=cid
            for i in range(p):
                store[space+i]=bits[(rot+i)%p]
                reps[space+i]=orbit[(rot+i)%p]
            space+=p
        else:cid=matched
        off=int(offsets[cid])
        for t in range(L):
            state=int(orbit[t]);phase=(t-rot)%p;rep=int(reps[off+phase])
            if save_reps:bystate[state]=rep
            if state==rep:continue
            q=0
            for j in range(width):q=T[q][2*((state>>j)&1)+((rep>>j)&1)]
            reader_checks+=1
            if not A[q]:
                return seen,cycles,classes,space,reader_checks,exact_matches,collisions,losses,max_orbit,state,rep,p,L,bystate
    return seen,cycles,classes,space,reader_checks,exact_matches,collisions,losses,max_orbit,-1,-1,0,0,bystate
reports=[];counter=None;BEGIN=time.monotonic()
for width in [8,*range(25,31)]:
    begin=time.monotonic();answer=partition(width,T,A,width<=8)
    seen,cycles,classes,profiles,checks,matches,hashcollisions,losses,largest,x,y,p,L,reps=answer
    report={'width':width,'states_checked':int(seen),'complete':seen==1<<width and x==-1,
      'permutation_cycles':int(cycles),'primitive_necklaces':int(classes),'distinct_column_profiles':int(profiles),
      'nontrivial_reader_checks':int(checks),'exact_necklace_matches':int(matches),'hash_collisions':int(hashcollisions),
      'cycles_with_shorter_head_period':int(losses),'maximum_orbit_period':int(largest),
      'seconds':round(time.monotonic()-begin,3)}
    reports.append(report);print(json.dumps(report),flush=True)
    if width<=8:(r/f'large-partition-representatives-{width}.json').write_text(json.dumps(reps.tolist())+'\n',encoding='utf-8')
    if x!=-1:
        counter={'width':width,'initial_a':int(x),'initial_b':int(y),'primitive_period':int(p),'orbit_period':int(L)}
        break
    if time.monotonic()-BEGIN>200:break
out={'reports':reports,'counterexample':counter,'finite_widths_only':True,'hash_matches_compared_exactly':True,
     'Lean_verified':False,'reader_completeness_proved':False,'full_problem_solved':False}
(r/'large-orbit-partition.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'counterexample':counter,'maximum_width_completed':reports[-1]['width'],
                  'seconds':round(time.monotonic()-BEGIN,3)}),flush=True)
