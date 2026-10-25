"""Independent scalar inverse and actual finite evolution controls.

The packed producer is imported only to obtain its claimed output. Its
bit recurrence, origin convention and evolution are not used by the checks.
"""
from pathlib import Path
import hashlib,json,time
from seam_core import Canonical,reconstruct
root=Path(__file__).resolve().parent;tick=time.monotonic()

def step(state):
    if not state:return set()
    result=set()
    for p in range(min(state)-1,max(state)+2):
        if (p-1 in state)!=((p in state) or (p+1 in state)):result.add(p)
    return result

def scalar_inverse(history,U,V,N):
    target=[int(0 in history[U+t]) for t in range(N+1)]
    row=[int(p in history[V]) for p in range(1,N+1)];right=[]
    for t in range(N):
        right.append(row[0]);row=[(row[i-1] if i else target[t])^(row[i]|row[i+1]) for i in range(len(row)-1)]
    R,C=right,target;negative=[]
    for _ in range(N):
        L=[C[t+1]^(C[t]|R[t]) for t in range(len(C)-1)]
        negative.append(L[0]);R,C=C,L
    return negative,target,right

data_path=root/'seam-probe.json';data=json.loads(data_path.read_text(encoding='utf-8'))
special=[data['failure'][k] for k in ['short','extended']] if data['failure'] else []
largest=max([80]+[r['U']+r['through'] for r in special]);history=[{0}]
for _ in range(largest):history.append(step(history[-1]))
packed=Canonical(largest+20);checks=0;forward=0;mutations=0;horizon=0
cases=[(U,V,32) for U in range(13) for V in range(U+1)]
cases += [(r['U'],r['V'],r['through']) for r in special]
for U,V,N in cases:
    r=reconstruct(packed,U,V,N);bits,target,right=scalar_inverse(history,U,V,N)
    assert int(r['negative_hex'],16)==sum(b<<(d-1) for d,b in enumerate(bits,1))
    assert int(r['center_trace_hex'],16)==sum(b<<t for t,b in enumerate(target))
    assert int(r['right_column_hex'],16)==sum(b<<t for t,b in enumerate(right))
    if U==V:
        assert { -d for d,b in enumerate(bits,1) if b}=={p for p in history[V] if p<0}
    outside=next((d for d,b in enumerate(bits,1) if d>V and b),None)
    assert outside==r['first_black_depth_beyond_V']
    initial={p for p in history[V] if p>0}|({0} if target[0] else set())|{-d for d,b in enumerate(bits,1) if b}
    state=set(initial)
    for t in range(N+1):assert int(0 in state)==target[t];state=step(state)
    forward+=N+1
    # The last inverse cell enters the last center observation with unit
    # coefficient, because Rule30 is left-permutive. Toggle that one cell.
    wrong=set(initial);wrong.symmetric_difference_update({-N})
    for t in range(N+1):
        assert int(0 in wrong)==(target[t]^(t==N));wrong=step(wrong)
    mutations+=1;checks+=1
    if U+N+5<len(packed.rows):
        extended=reconstruct(packed,U,V,N+5)
        assert int(extended['negative_hex'],16)&((1<<N)-1)==int(r['negative_hex'],16)
        horizon+=1
if data['failure']:
    short,extended=[data['failure'][k] for k in ['short','extended']]
    assert short['through']==short['U']+1 and short['initial_center_matches_younger']
    assert int(short['negative_hex'],16)>>short['V']==0
    assert extended['first_black_depth_beyond_V'] is None or extended['first_black_depth_beyond_V']>short['through']
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'scalar_inverse_controls':checks,'forward_center_controls':forward,
     'last_cell_corruptions_rejected':mutations,'horizon_consistency_controls':horizon,
     'short_deadline_failure_independently_confirmed':bool(data['failure']),
     'input_sha256':hashlib.sha256(data_path.read_bytes()).hexdigest(),'seconds':time.monotonic()-tick,
     'scope':'Finite independent inversion and physical forward replay; no unbounded escape theorem.'}
(root/'seam-independent-verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
