"""All width-20 actual finite right halves, finite trap-entry horizon 128."""
from pathlib import Path
from fractions import Fraction
import json,time
import numpy as np
import feedback_core as core
root=Path(__file__).resolve().parent;start=time.monotonic()
W=20;H=128;N=1<<W
codes=np.arange(N,dtype=np.uint64)<<np.uint64(1)
rows=np.zeros((3,N),dtype=np.uint64);rows[0]=codes|np.uint64(1)
lookup=np.zeros((4,1<<19),dtype=np.bool_)
for phase in range(4):
    ether=sum(core.table[(3+p)%7][phase]<<(p-1) for p in range(1,7))
    for wall in core.wallsets[phase]:lookup[phase,ether|(wall<<6)]=True
found_time=np.full(N,-1,dtype=np.int16);found_phase=np.full(N,-1,dtype=np.int8)
check_indices=[0,1,0x888>>1,0x72270>>1,(1<<W)-1,0x7bd55]
scalar=[int(codes[i])|1 for i in check_indices]
controls=0;history=[]
for t in range(H+1):
    for i,a in zip(check_indices,scalar):
        assert all(int(rows[k,i])==((a>>(64*k))&((1<<64)-1)) for k in range(3))
        controls+=1
    word=((rows[0]>>np.uint64(1))&np.uint64((1<<19)-1)).astype(np.int64)
    for s in (1,3):
        phase=(t+s)%4;hit=lookup[phase,word]&(found_time<0)
        found_time[hit]=t;found_phase[hit]=phase
    if t%16==0:
        rec={'time':t,'found':int(np.count_nonzero(found_time>=0)),'elapsed_seconds':time.monotonic()-start}
        history.append(rec);print(json.dumps(rec),flush=True)
    if t==H:break
    left=rows<<np.uint64(1);left[1:]|=rows[:-1]>>np.uint64(63)
    right=rows>>np.uint64(1);right[:-1]|=rows[1:]<<np.uint64(63)
    rows=left^(rows|right)
    rows[0]&=np.uint64((1<<64)-2);rows[0]|=np.uint64(int((t+1)%2==0))
    scalar=[core.step(a,t) for a in scalar]
np.savez_compressed(root/'width20-trap-entries.npz',time=found_time,phase=found_phase)
assert found_time[0x888>>1]>=0 and found_time[0x72270>>1]>=0
indices=np.flatnonzero(found_time>=0)
cache={};representatives=[];best=None;stop=None
with (root/'exhaustive-traps.partial.jsonl').open('w',encoding='utf-8') as log:
    for i in indices:
        if time.monotonic()-start>230:stop='internal_time_budget';break
        code=int(codes[i]);T=int(found_time[i]);trap=core.trapped(code,cap=T)
        assert trap is not None
        key=(tuple(trap['free_prefix']),trap['tail_first'])
        if key in cache:continue
        cycle=core.spatial_cycle(*key);cache[key]=cycle
        actual=core.free_stream(code,max(256,len(key[0])+64))
        assert actual==list(key[0])+[key[1]^(j%2) for j in range(len(actual)-len(key[0]))]
        rec={'initial_right_hex':hex(code),'trap':trap,'spatial_cycle':cycle}
        representatives.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
        if 'period' in cycle and (best is None or Fraction(cycle['density'])<Fraction(best['spatial_cycle']['density'])):
            best=rec;print(json.dumps({'new_actual_minimum':rec}),flush=True)
        if cycle.get('C3_positive_drift'):stop='actual_finite_right_C3_counterexample_candidate';break
hist={}
for c in cache.values():
    k=c.get('density','unknown');hist[k]=hist.get(k,0)+1
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'width':W,'finite_horizon':H,'initial_rows':N,'trap_ether_width_checked':6,
     'entry_count':len(indices),'distinct_eventual_streams_examined':len(cache),
     'representatives':representatives,'density_histogram':hist,'best_actual':best,
     'independent_full_row_controls':controls,'history':history,'stop':stop,
     'elapsed_seconds':time.monotonic()-start,
     'scope':'All width-20 finite initial rows checked to time 128 for width-six catalog trap. Omitted entries and incomplete cycle searches are unknown. No all-width or Lean claim.'}
(root/'exhaustive-traps.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['entry_count','distinct_eventual_streams_examined','density_histogram','stop','elapsed_seconds']}))
