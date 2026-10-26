"""Falsify a low-three-bit replacement for exact canonical ancestry."""
from pathlib import Path
import json,time
from backward_fields import kernel
root=Path(__file__).resolve().parent;started=time.monotonic()
def cls0(x):
    if not x:return True
    while x%2==0:x>>=1
    return ((x>>1)&1)==((x>>2)&1)
def add(pivots,row):
    while row:
        p=row.bit_length()-1
        if p not in pivots:pivots[p]=row;break
        row^=pivots[p]
cases=0;counter=None;summary=[]
for L in range(2,9):
    mask=(1<<(L+1))-1;bound=(1<<L)*(1<<(L-1).bit_length());count=0
    for a0 in range(1,1<<(L+1),2):
        if not cls0(a0):continue
        for b0 in range(0,1<<(L+1),2):
            if not cls0(b0):continue
            cases+=1;count+=1
            delta=a0^b0;positions=[j for j in range(L) if delta>>j&1];n=len(positions)
            fields=[0]*L
            for i,j in enumerate(positions):fields[j]=1<<i
            initial=tuple(fields);a,b=a0,b0;pivots={};killed=False
            for t in range(bound):
                delta=a^b
                for j in range(1,L+1):
                    row=((fields[j-1] if delta>>j&1 else 0)^ \
                         (fields[j] if j<L and delta>>(j-1)&1 else 0))
                    add(pivots,row)
                nxt=[]
                for j in range(L+2):
                    row=(fields[j] if j<L else 0)^ \
                        (fields[j-1] if 0<=j-1<L and not(b>>(j-2)&1 if j>=2 else 0) else 0)^ \
                        (fields[j-2] if 0<=j-2<L and not(a>>(j-1)&1) else 0)
                    nxt.append(row)
                for row in nxt[L:]:add(pivots,row)
                if len(pivots)==n:killed=True;break
                fields=nxt[:L]
                a=(a^((a<<1)|(a<<2)))&mask;b=(b^((b<<1)|(b<<2)))&mask
            if not killed:
                assert a==a0 and b==b0 and tuple(fields)==initial
                v=kernel(list(pivots.values()),n)[0]
                counter={'L':L,'A_low_prefix':a0,'B_low_prefix':b0,
                         'h_initial_depths':[p for i,p in enumerate(positions) if v>>i&1],
                         'checked_return_period':bound,'exact_canonical_ancestry':False}
                break
        if counter:break
    summary.append({'L':L,'cases':count});print(json.dumps(summary[-1]),flush=True)
    if counter:break
out={'finite_prefix_scope_only':True,'Lean_verified':False,'cases':cases,'summaries':summary,
     'older_low_class_zero_required':True,'younger_low_class_zero_required':True,
     'initial_subset_required':True,
     'low_class_replacement_counterexample':counter,'full_problem_solved':False,
     'seconds':time.monotonic()-started}
(root/'prefix-class-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
