"""Falsification, not a general observability theorem."""
from pathlib import Path
import json,time
from observer_core import observer

root=Path(__file__).resolve().parent;start=time.monotonic()
records=[];unresolved=[];counts={};stop=None
with (root/'observer-adversarial.partial.jsonl').open('w',encoding='utf-8') as log:
    def test(W,a,b,kind):
        r=observer(W,0,30,cap=12*W+96,initial_pair=(a,b))
        r.update(A_hex=hex(a),B_hex=hex(b),kind=kind)
        counts[kind]=counts.get(kind,0)+1
        if r['unresolved']:unresolved.append(r)
        if r['unresolved'] or r['certificate']['observed_through']>3*W+8:
            records.append(r);log.write(json.dumps(r)+'\n');log.flush()
        return r
    # Full finite pairs: the longer row has the farther-left edge, and B may
    # be zero or may first be nonzero on either side of the observation column.
    for W in range(1,5):
        K=2*W+1
        for a in range(1,1<<K,2):
            for b in range(0,1<<K,2):
                if time.monotonic()-start>210:stop='internal_time_budget';break
                r=test(W,a,b,'exhaustive_W'+str(W))
                if len(unresolved)>=4:stop='four_unresolved';break
            if stop:break
        print(json.dumps({'W':W,'counts':counts,'unresolved':len(unresolved),'seconds':time.monotonic()-start}),flush=True)
        if stop:break
    # Periodic words and truncations are structured adverse controls, since
    # uniform zero backgrounds have reflection modes invisible at the center.
    if not stop:
        for W in (6,12,24,48):
            K=2*W+1;mask=(1<<K)-1
            words=[sum(((pat>>(i%period))&1)<<i for i in range(K))
                   for period in range(1,6) for pat in range(1,1<<period)]
            for a in sorted(set((v|1) for v in words)|{1,mask,49}):
                for b in sorted(set((v&~1) for v in words)|{0,48}):
                    if time.monotonic()-start>230:stop='internal_time_budget';break
                    test(W,a,b,'structured_W'+str(W))
                    if len(unresolved)>=4:stop='four_unresolved';break
                if stop:break
            if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'counts':counts,'unresolved':unresolved,'interesting_records':records,
     'stop':stop,'seconds':time.monotonic()-start,
     'scope':'Capped non-recovery is unknown, not a counterexample. Exact identities checked in every case. No unbounded theorem.'}
(root/'observer-adversarial.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['unresolved','interesting_records']}),flush=True)
