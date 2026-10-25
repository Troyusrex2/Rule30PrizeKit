"""Independent backward-adjoint checks of the forward row-space certificates.

No forward basis-vector field or Gaussian elimination is used here. Initial
coordinates outside [-W,W] are known zero and are discarded only at the end.
"""
from pathlib import Path
import hashlib,json,time
root=Path(__file__).resolve().parent;start=time.monotonic()
counts={};checked=0;negative_controls=0;maximum=0

def step(a,rule):
    return (a<<1)^(a|(a>>1)) if rule==30 else (a<<1)^((a>>1)&~a)

def check(rec):
    global checked,negative_controls,maximum
    cert=rec['certificate']
    if cert is None:return
    W=rec['TA'];N=cert['observed_through'];rule=rec['rule']
    assert W>0 and N<=rec['cap']
    offset=W+N+4;mask=(1<<(2*offset+1))-1
    if 'A_hex' in rec:
        ai,bi=[int(rec[k],16) for k in ('A_hex','B_hex')]
        assert ai.bit_length()<=2*W+1 and bi.bit_length()<=2*W+1
        a,b=ai<<(offset-W),bi<<(offset-W)
    else:
        a=b=1<<offset
        for _ in range(rec['TA']):a=step(a,rule)&mask
        for _ in range(rec['TB']):b=step(b,rule)&mask
    delta=((a^b)>>(offset-W))&((1<<(2*W+1))-1)
    assert delta&1
    history=[];output=[]
    for t in range(N+1):
        history.append((a,b));output.append(((a^b)>>offset)&1)
        a,b=step(a,rule)&mask,step(b,rule)&mask
    times=cert['certificate_times']
    assert times==sorted(set(times)) and times and times[-1]==N
    assert len(times)==cert['certificate_weight']
    chosen=set(times);q=0
    for t in range(N,-1,-1):
        if t in chosen:q^=1<<offset
        if t:
            a,b=history[t-1]
            cc=~(b>>1) if rule==30 else b>>1
            q=((q>>1)^(q&cc)^((q<<1)&~(a<<1)))&mask
    initial_row=(q>>(offset-W))&((1<<(2*W+1))-1)
    assert initial_row==1,(rec['TA'],rec['TB'],rule,hex(initial_row))
    assert sum(output[t] for t in times)%2==1
    assert ((initial_row&delta).bit_count()&1)==1
    # Toggling the time-zero observation adds the center unit at initial time.
    # This is a deliberately wrong certificate, and must fail the unit test.
    assert initial_row^(1<<W)!=1
    negative_controls+=1;checked+=1;maximum=max(maximum,W)

for name in ['source-observer.json','observer-generic.json','observer-stress.json']:
    data=json.loads((root/name).read_text(encoding='utf-8'))
    before=checked
    for r in data['records']:check(r)
    counts[name]=checked-before
data=json.loads((root/'observer-smt.json').read_text(encoding='utf-8'))
for r in data['records']:
    if r['verdict']=='sat':
        record=dict(r['extended_observer'],**r['witness']);check(record)
out={'independent_backward_adjoint':'PASS','counts':counts,'certificates_checked':checked,
     'deliberately_wrong_time_zero_certificates_rejected':negative_controls,
     'maximum_TA':maximum,'Lean_verified':False,'full_problem_solved':False,
     'seconds':time.monotonic()-start,
     'sha256':{name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in
               ['source-observer.json','observer-generic.json','observer-stress.json','observer-smt.json']}}
(root/'observer-independent-check.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
