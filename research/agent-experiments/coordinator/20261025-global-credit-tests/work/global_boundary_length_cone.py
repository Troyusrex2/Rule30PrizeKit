"""Seek an integer obstruction to ANY global boundary-and-length block rank.
If a nonzero positive integer combination of guarded event differences has
old blocks componentwise contained in new blocks, no strictly decreasing
multiset measure of descriptors can satisfy all those events. No parent
assignment, affine block rank or finite rank bound is imposed.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction
from functools import reduce
from math import gcd,lcm
import hashlib,json,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix,csr_matrix
root=Path(__file__).resolve().parent;started=time.monotonic();N=4096;P=16
def phi(a):return a^((a<<1)|(a<<2))
def runs(d):
    while d:
        lo=(d&-d).bit_length()-1;n=((d>>lo)^((d>>lo)+1)).bit_length()-1
        yield lo,n;d&=~(((1<<n)-1)<<lo)
def describe(a,b,lo,length,n):
    def pair(i):return ((a>>i)&1)|(((b>>i)&1)<<1) if i>=0 else 0
    # Unbounded length is retained; internal letters beyond the endpoints
    # are forgotten. This is broader than affine-length scores, but narrower
    # than arbitrary full-word ranks.
    return (n%16,pair(lo-1),length,pair(lo),pair(lo+length-1),pair(lo+length))
def solve(deltas,cost):
    vocabulary=sorted({f for d in deltas for f in d});ids={v:i for i,v in enumerate(vocabulary)}
    ri=[];ci=[];values=[]
    for j,d in enumerate(deltas):
        for f,v in d.items():
            if v:ri.append(ids[f]);ci.append(j);values.append(v)
    A=coo_matrix((values,(ri,ci)),shape=(len(vocabulary),len(deltas)),dtype=np.float64).tocsr()
    answer=linprog(np.asarray(cost,dtype=float),A_ub=A,b_ub=np.zeros(len(vocabulary)),
                   A_eq=np.ones((1,len(deltas))),b_eq=[1.],bounds=(0,None),
                   method='highs',options={'time_limit':45.,'presolve':True})
    info={'status':answer.status,'message':answer.message,'descriptor_types':len(vocabulary),'events':len(deltas),'nonzero_entries':A.nnz}
    if answer.success:
        support=[j for j,v in enumerate(answer.x) if v>1e-9]
        fractions=[Fraction(float(answer.x[j])).limit_denominator(10**9) for j in support]
        den=lcm(*(f.denominator for f in fractions));weights=[f.numerator*(den//f.denominator) for f in fractions]
        div=reduce(gcd,weights);weights=[w//div for w in weights]
        combined=Counter()
        for j,w in zip(support,weights):
            for f,v in deltas[j].items():combined[f]+=w*v
        exact=bool(weights) and all(w>0 for w in weights) and all(v<=0 for v in combined.values())
        info.update({'support':support,'integer_weights':weights,'exact_integer_certificate':exact,
                     'positive_coordinate_violations':sum(v>0 for v in combined.values()),
                     'largest_positive_error':max([v for v in combined.values() if v>0],default=0),
                     'strictly_negative_coordinates':sum(v<0 for v in combined.values())})
    return info

# Positive and negative controls for the cone criterion itself.
yes=solve([{'a':1,'b':-1},{'a':-1,'b':1}],[0,1]);assert yes['exact_integer_certificate']
no=solve([{'a':1}],[0]);assert no['status']==2
rows=[1]
for _ in range(N+P+2):rows.append(phi(rows[-1]))
events=[];deltas=[]
for n in range(N):
    if not all((rows[n+i]>>(n+i)&1)==(rows[n+P+i]>>(n+P+i)&1) for i in range(3)):continue
    a,b=rows[n]<<P,rows[n+P];an,bn=rows[n+2]<<P,rows[n+P+2]
    old=Counter(describe(a,b,lo,le,n) for lo,le in runs(a^b))
    new=Counter(describe(an,bn,lo,le,n+2) for lo,le in runs(an^bn))
    delta=old.copy();delta.subtract(new);delta={f:c for f,c in delta.items() if c}
    events.append(n);deltas.append(delta)
result=solve(deltas,[n/N for n in events])
if 'support' in result:result['support_onsets']=[events[j] for j in result['support']]
out={'finite_only':True,'Lean_verified':False,'distinct_onsets':N,'lag':P,'phase_clock':16,'halo':1,
     'descriptor':'phase,left halo,unbounded run length,first pair,last pair,right halo; internal word forgotten',
     'controls':{'two_event_cycle':yes,'single_deletion':no},'result':result,
     'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'An exact integer certificate would obstruct global ordinal multiset descent for boundary/phase/length descriptors without causal credit rules or an affine restriction. Full-word and position/history-dependent ranks remain separate. Floating infeasibility, timeout, or unsuccessful rational reconstruction is not a theorem.'}
(root/'global-boundary-length-cone.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
