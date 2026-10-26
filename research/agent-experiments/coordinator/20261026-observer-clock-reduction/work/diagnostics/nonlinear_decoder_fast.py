"""Compiled GF(2) algebra, cross-checked against the Python implementation.
Test the new cubic-decoder hypothesis at the next width, and raw coordinates.
This is finite algebra evidence, not an all-width decoder proof.
"""
from pathlib import Path
import json,time,numpy as np
from numba import njit
r=Path(__file__).resolve().parent;START=time.monotonic()
@njit(cache=False)
def highbit(x):
    p=0
    for shift in [32,16,8,4,2,1]:
        if x>>shift:x>>=shift;p+=shift
    return p
@njit(cache=False)
def add(v,basis,has,store):
    for w in range(len(v)-1,-1,-1):
        while v[w]:
            p=64*w+highbit(v[w])
            if has[p]:
                for k in range(w+1):v[k]^=basis[p,k]
            else:
                if store:
                    has[p]=True
                    for k in range(w+1):basis[p,k]=v[k]
                return True
    return False
@njit(cache=False)
def add_matrix(vectors,basis,has):
    n=0
    for i in range(vectors.shape[0]):
        if add(vectors[i].copy(),basis,has,True):n+=1
    return n
@njit(cache=False)
def product_layer(previous,linear,basis,has):
    v=np.empty(basis.shape[1],dtype=np.uint64);new=0
    for i in range(previous.shape[0]):
      for j in range(linear.shape[0]):
        for k in range(len(v)):v[k]=previous[i,k]&linear[j,k]
        if add(v,basis,has,True):new+=1
    return new
def encode(z,m):
    xs=[(z>>i)&1 for i in range(m)];i=next((i for i,x in enumerate(xs) if x),m)
    return [0]+xs if i>=m-2 else xs[:i+2]+[xs[i+1]]+xs[i+2:]
def pack(v):
    bb=np.packbits(v,bitorder='little');bb=np.pad(bb,(0,(-len(bb))%8))
    return bb.view(np.uint64)
old={x['width']:x for x in json.loads((r/'nonlinear-decoder-probe.json').read_bytes())['reports']}
reports=[]
for n in range(3,15):
    begin=time.monotonic();m=n-1;M=1<<m;P=1<<((2*n-1)//3);W=(M+63)//64
    rows=np.array([sum(x<<i for i,x in enumerate(encode(z,m))) for z in range(M)],dtype=np.uint32)
    initial=rows.copy();obs=np.zeros((P,W),dtype=np.uint64)
    for t in range(P):
        obs[t]=pack((rows>>(n-1))&1)
        rows=(rows^((rows<<1)|(rows<<2)))&((1<<n)-1)
    assert np.array_equal(rows,initial)
    targets=np.array([pack((np.arange(M,dtype=np.uint32)>>j)&1) for j in range(m)])
    rawtargets=np.array([pack((initial>>j)&1) for j in range(n)])
    basis=np.zeros((M,W),dtype=np.uint64);has=np.zeros(M,dtype=np.bool_)
    add(pack(np.ones(M,dtype=np.uint8)),basis,has,True)
    add_matrix(obs,basis,has);linear=basis[has].copy();layers=[]
    for degree in range(1,4):
        if degree>1:product_layer(basis[has].copy(),linear,basis,has)
        recovered=[j for j in range(m) if not add(targets[j].copy(),basis,has,False)]
        raw_recovered=[j for j in range(n) if not add(rawtargets[j].copy(),basis,has,False)]
        layer={'degree':degree,'rank':int(has.sum()),'recovered_coordinates':recovered,'raw_recovered_coordinates':raw_recovered}
        if n in old:
            oldlayer=next((x for x in old[n]['layers'] if x['degree']==degree),None)
            if oldlayer is not None:
                assert layer['rank']==oldlayer['rank'] and recovered==oldlayer['recovered_coordinates'],(n,degree,layer,oldlayer)
        layers.append(layer)
        if len(recovered)==m and len(raw_recovered)==n:break
    report={'width':n,'rows':M,'working_period':P,'layers':layers,
            'cubic_code_recovery':len(recovered)==m,'cubic_raw_recovery':len(raw_recovered)==n,
            'cross_checked_with_python':n in old,
            'seconds':round(time.monotonic()-begin,3)}
    reports.append(report);print(json.dumps(report),flush=True)
    (r/'nonlinear-decoder-fast.json').write_text(json.dumps({'reports':reports,
        'Lean_verified':False,'canonical_observer_proved':False,'full_problem_solved':False,
        'seconds':round(time.monotonic()-START,3)},indent=2)+'\n',encoding='utf-8')
    if not report['cubic_code_recovery']:break
