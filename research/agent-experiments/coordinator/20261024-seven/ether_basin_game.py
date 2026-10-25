"""Exact universal-entry game on a 19-cell driven prefix.

The exterior cell is adversarial and may be unrealizable by any finite right
half. Losing this game is not a counterexample to absorption or CQ01.
"""
import hashlib,json,time
import numpy as np
from numba import njit
from core import HERE,save
from empty_right_absorption import patterns,match

@njit
def successors(w):
    n=1<<w;N=4*n;mask=n-1
    a=np.empty(N,np.int32);b=np.empty(N,np.int32)
    for phase in range(4):
        base=((phase+1)%4)*n;driver=1 if phase%2==0 else 0
        for x in range(n):
            y=((x<<1)|driver)^(x|(x>>1));i=phase*n+x
            a[i]=base+(y&mask)
            b[i]=base+((y^(0 if x>>(w-1)&1 else 1<<(w-1)))&mask)
    return a,b

@njit
def basin(a,b,seeds):
    N=len(a);degree=np.zeros(N,np.int32)
    for i in range(N):degree[a[i]]+=1;degree[b[i]]+=1
    ptr=np.empty(N+1,np.int32);ptr[0]=0
    for i in range(N):ptr[i+1]=ptr[i]+degree[i]
    cursor=ptr[:-1].copy();incoming=np.empty(2*N,np.int32)
    for i in range(N):
        incoming[cursor[a[i]]]=i;cursor[a[i]]+=1
        incoming[cursor[b[i]]]=i;cursor[b[i]]+=1
    rank=np.full(N,-1,np.int32);remaining=np.full(N,2,np.int8)
    depth=np.zeros(N,np.int32);queue=np.empty(N,np.int32);head=0;tail=0
    for x in seeds:
        if rank[x]<0:rank[x]=0;queue[tail]=x;tail+=1
    while head<tail:
        y=queue[head];head+=1
        for j in range(ptr[y],ptr[y+1]):
            x=incoming[j]
            if rank[x]>=0:continue
            remaining[x]-=1
            if rank[y]+1>depth[x]:depth[x]=rank[y]+1
            if remaining[x]==0:
                rank[x]=depth[x];queue[tail]=x;tail+=1
    for i in range(N):
        if rank[i]<0:assert rank[a[i]]<0 or rank[b[i]]<0
        elif rank[i]>0:assert 0<=rank[a[i]]<rank[i] and 0<=rank[b[i]]<rank[i]
    return rank

def controls():
    rng=np.random.default_rng(302432);cases=0
    for w in range(2,7):
        a,b=successors(w);N=len(a)
        seed=np.array(sorted(set(map(int,rng.integers(N,size=N//5)))),dtype=np.int32)
        fast=basin(a,b,seed);slow=set(map(int,seed))
        while True:
            new={i for i in range(N) if int(a[i]) in slow and int(b[i]) in slow}
            if new<=slow:break
            slow|=new
        assert slow==set(map(int,np.flatnonzero(fast>=0)));cases+=N
        for phase in range(4):
            for x in range(1<<w):
                for exterior,dest in [(0,a[phase*(1<<w)+x]),(1,b[phase*(1<<w)+x])]:
                    old=[1 if phase%2==0 else 0]+[(x>>j)&1 for j in range(w)]+[exterior]
                    expected=sum(((30>>((old[j]<<2)|(old[j+1]<<1)|old[j+2]))&1)<<j for j in range(w))
                    assert int(dest)==((phase+1)%4)*(1<<w)+expected
    return {'states_compared_with_naive_fixed_point':cases,'all_passed':True}

def main():
    checked=controls();start=time.monotonic();w=19;n=1<<w
    low,walls,sha=patterns();seeds=[]
    for phase in range(4):
        for offset in (1,3):
            p=(phase+offset)%4
            seeds += [phase*n+low[p]+(wall<<6) for wall in walls[p]]
    seeds=np.array(sorted(set(seeds)),dtype=np.int32);a,b=successors(w);rank=basin(a,b,seeds)
    assert all(match(int(i)%n,int(i)//n,low,walls) is not None for i in seeds)
    counts=np.bincount(rank[rank>=0]);late=json.loads((HERE/'empty-right-absorption.json').read_text())
    raw=(HERE/'empty-right-absorption-state.bin').read_bytes();assert hashlib.sha256(raw).hexdigest()==late['state_sha256']
    late_index=(late['last_checked_time']%4)*n+(int.from_bytes(raw,'little')&(n-1))
    # One adversarial path from zero, recording a finite lasso if it repeats.
    node=0;seen={};choices=[]
    while rank[node]<0 and node not in seen:
        seen[node]=len(choices)
        if rank[a[node]]<0:choices.append(0);node=int(a[node])
        else:choices.append(1);node=int(b[node])
    lasso=None if rank[node]>=0 else {'stem':seen[node],'period':len(choices)-seen[node],
                                    'exterior_choices':choices}
    out={'prefix_width':w,'phase_states':4,'nodes':4*n,'seed_traps':len(seeds),
         'winning_nodes':int(np.count_nonzero(rank>=0)),'max_entry_bound':len(counts)-1,
         'winning_counts_by_entry_bound':list(map(int,counts)),
         'empty_prefix_entry_bound':int(rank[0]),'late_empty_time':late['last_checked_time'],
         'late_empty_prefix_entry_bound':int(rank[late_index]),'adversarial_lasso':lasso,
         'controls':checked,'official_ether_source_sha256':sha,'Lean_verified':False,
         'CQ01Empty_proved':False,'full_problem_solved':False,
         'losing_means_only_universal_prefix_test_failed':True,'seconds':round(time.monotonic()-start,3)}
    save('ether-basin-game.json',out)
    print({k:v for k,v in out.items() if k not in ('adversarial_lasso','winning_counts_by_entry_bound')},flush=True)

if __name__=='__main__':main()
