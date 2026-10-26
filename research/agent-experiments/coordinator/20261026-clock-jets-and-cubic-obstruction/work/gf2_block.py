"""Packed GF(2) row reduction with eight-pivot lookup blocks.
Tables are discarded after each block; no guard limits are changed.
"""
import numpy as np
from numba import njit
@njit(cache=False)
def highbit(x):
    p=0
    for shift in [32,16,8,4,2,1]:
        if x>>shift:x>>=shift;p+=shift
    return p
@njit(cache=False)
def pivot(row):
    for w in range(len(row)-1,-1,-1):
        if row[w]:return 64*w+highbit(row[w])
    return -1
@njit(cache=False)
def bit(row,p):return (row[p//64]>>(p%64))&np.uint64(1)
@njit(cache=False)
def parity(x):
    for shift in [32,16,8,4,2,1]:x^=x>>shift
    return int(x&np.uint64(1))
@njit(cache=False)
def eliminate(matrix,target):
    end=matrix.shape[0];W=matrix.shape[1];rank=0;pivots=np.empty(end,dtype=np.int64)
    while rank<end:
        count=0
        while count<8 and rank+count<end:
            row=rank+count
            for j in range(count):
                if bit(matrix[row],pivots[rank+j]):
                    for w in range(W):matrix[row,w]^=matrix[rank+j,w]
            p=pivot(matrix[row])
            if p<0:
                end-=1
                for w in range(W):matrix[row,w],matrix[end,w]=matrix[end,w],matrix[row,w]
                continue
            pivots[row]=p;count+=1
        if count==0:break
        size=1<<count;table=np.zeros((size,W),dtype=np.uint64);inverse=np.zeros(size,dtype=np.int64)
        for v in range(1,size):
            low=v&-v;j=0
            while (1<<j)!=low:j+=1
            for w in range(W):table[v,w]=table[v^low,w]^matrix[rank+j,w]
            pattern=0
            for k in range(count):pattern|=int(bit(table[v],pivots[rank+k]))<<k
            assert pattern!=0 and inverse[pattern]==0
            inverse[pattern]=v
        for row in range(rank+count,end):
            pattern=0
            for k in range(count):pattern|=int(bit(matrix[row],pivots[rank+k]))<<k
            v=inverse[pattern]
            if v:
                for w in range(W):matrix[row,w]^=table[v,w]
        pattern=0
        for k in range(count):pattern|=int(bit(target,pivots[rank+k]))<<k
        v=inverse[pattern]
        if v:
            for w in range(W):target[w]^=table[v,w]
        rank+=count
    return rank,pivots[:rank]
@njit(cache=False)
def dual_vector(matrix,pivots,free):
    W=matrix.shape[1];dual=np.zeros(W,dtype=np.uint64)
    dual[free//64]|=np.uint64(1)<<np.uint64(free%64)
    for i in range(len(pivots)-1,-1,-1):
        x=np.uint64(0)
        for w in range(W):x^=matrix[i,w]&dual[w]
        if parity(x):dual[pivots[i]//64]^=np.uint64(1)<<np.uint64(pivots[i]%64)
    return dual
@njit(cache=False)
def features(obs,M):
    P,W=obs.shape;R=1+P+P*(P-1)//2+P*(P-1)*(P-2)//6
    mat=np.zeros((R,W),dtype=np.uint64);mat[0,:]=np.uint64(0xffffffffffffffff)
    if M%64:mat[0,-1]=(np.uint64(1)<<np.uint64(M%64))-np.uint64(1)
    row=1
    for i in range(P):
        mat[row,:]=obs[i];row+=1
    for i in range(P):
      for j in range(i+1,P):
        for w in range(W):mat[row,w]=obs[i,w]&obs[j,w]
        row+=1
    for i in range(P):
      for j in range(i+1,P):
       for k in range(j+1,P):
        for w in range(W):mat[row,w]=obs[i,w]&obs[j,w]&obs[k,w]
        row+=1
    assert row==R
    return mat
