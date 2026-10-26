"""Test exact finite right cones for defect streams, with physical SAT controls.
SAT/UNSAT from Z3 is diagnostic only; no Lean or unbounded conclusion follows.
"""
from pathlib import Path
import json,sys,time
sys.path.insert(0,r'D:\MWB\Rule30\wolfram-local\z3-deps')
import z3
ROOT=Path(__file__).resolve().parent

def free_physical(initial,n):
    row={j+1 for j in range(initial.bit_length()) if initial>>j&1};out=[]
    for t in range(2*n-1):
        left=t%2==0
        row={p for p in range(1,max(row,default=0)+2)
             if ((left if p==1 else p-1 in row) ^ ((p in row) or (p+1 in row)))}
        if t%2==0:out.append(int(1 not in row))
    return out

def solve(f):
    n=len(f);s=z3.Solver();s.set(timeout=4000,max_memory=1024)
    initial=[z3.Bool('x_'+str(j)) for j in range(2*n)];row=initial
    for t in range(2*n-1):
        nxt=[z3.Bool(f'a_{t+1}_{j}') for j in range(len(row)-1)]
        for j,v in enumerate(nxt):
            s.add(v==z3.Xor(z3.BoolVal(t%2==0) if j==0 else row[j-1],z3.Or(row[j],row[j+1])))
        row=nxt
        if t%2==0:s.add(row[0]==z3.BoolVal(not f[t//2]))
    start=time.monotonic();status=s.check()
    result={'bits':n,'status':str(status),'seconds':round(time.monotonic()-start,4)}
    if status==z3.sat:
        m=s.model();right=sum(int(z3.is_true(m.eval(q,model_completion=True)))<<j for j,q in enumerate(initial))
        assert free_physical(right,n)==f
        result.update({'physical_witness_replayed':True,'right_initial_hex':hex(right)})
    elif status==z3.unknown:result['reason_unknown']=s.reason_unknown()
    return result
