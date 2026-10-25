"""Disjoint exhaustive width-24 chunks; stop at a real C3 candidate or owned budget."""
from pathlib import Path
from fractions import Fraction
import json,time
import numpy as np
import feedback_core as core
root=Path(__file__).resolve().parent;start=time.monotonic()
W=24;H=128;chunk=1<<20
lookup=np.zeros((4,1<<19),dtype=np.bool_)
for phase in range(4):
    ether=sum(core.table[(3+p)%7][phase]<<(p-1) for p in range(1,7))
    for wall in core.wallsets[phase]:lookup[phase,ether|(wall<<6)]=True
old=json.loads((root/'exhaustive-traps.json').read_text())
cache={(tuple(r['trap']['free_prefix']),r['trap']['tail_first']):r['spatial_cycle'] for r in old['representatives']}
representatives=[];best=old['best_actual'];chunks=[];stop=None;controls=0
with (root/'width24-traps.partial.jsonl').open('w',encoding='utf-8') as log:
    for high in range(1,16): # chunk zero is already exhaustively archived
        if time.monotonic()-start>220:stop='internal_time_budget';break
        codes=(np.arange(chunk,dtype=np.uint64)+np.uint64(high*chunk))<<np.uint64(1)
        rows=np.zeros((3,chunk),dtype=np.uint64);rows[0]=codes|np.uint64(1)
        found=np.full(chunk,-1,dtype=np.int16)
        ci=[0,0x4444,chunk-1];scalar=[int(codes[i])|1 for i in ci]
        completed=True
        for t in range(H+1):
            if time.monotonic()-start>230:stop='internal_time_budget';completed=False;break
            for i,a in zip(ci,scalar):
                assert all(int(rows[k,i])==((a>>(64*k))&((1<<64)-1)) for k in range(3))
                controls+=1
            word=((rows[0]>>np.uint64(1))&np.uint64((1<<19)-1)).astype(np.int64)
            hit=(lookup[(t+1)%4,word]|lookup[(t+3)%4,word])&(found<0)
            found[hit]=t
            if t==H:break
            left=rows<<np.uint64(1);left[1:]|=rows[:-1]>>np.uint64(63)
            right=rows>>np.uint64(1);right[:-1]|=rows[1:]<<np.uint64(63)
            rows=left^(rows|right)
            rows[0]&=np.uint64((1<<64)-2);rows[0]|=np.uint64(int((t+1)%2==0))
            scalar=[core.step(a,t) for a in scalar]
        indices=np.flatnonzero(found>=0)
        np.savez_compressed(root/f'width24-chunk{high:02d}-entries.npz',indices=indices,time=found[indices])
        classified=0
        for i in indices:
            if time.monotonic()-start>230:stop='internal_time_budget';break
            code=int(codes[i]);trap=core.trapped(code,cap=int(found[i]));assert trap is not None
            key=(tuple(trap['free_prefix']),trap['tail_first'])
            if key in cache:classified+=1;continue
            cycle=core.spatial_cycle(*key);cache[key]=cycle
            actual=core.free_stream(code,max(256,len(key[0])+64))
            assert actual==list(key[0])+[key[1]^(j%2) for j in range(len(actual)-len(key[0]))]
            rec={'initial_right_hex':hex(code),'trap':trap,'spatial_cycle':cycle}
            representatives.append(rec);log.write(json.dumps(rec)+'\n');log.flush();classified+=1
            if 'period' in cycle and Fraction(cycle['density'])<Fraction(best['spatial_cycle']['density']):
                best=rec;print(json.dumps({'new_actual_minimum':rec}),flush=True)
            if cycle.get('C3_positive_drift'):stop='actual_finite_right_C3_counterexample_candidate';break
        info={'chunk':high,'code_index_begin_inclusive':high*chunk,
              'code_index_end_exclusive':(high+1)*chunk,'completed_time':t,
              'full_horizon_checked':completed,'trap_entries':len(indices),'entries_classified':classified,
              'distinct_streams_total_including_width20':len(cache),'elapsed_seconds':time.monotonic()-start}
        chunks.append(info);print(json.dumps(info),flush=True)
        if stop:break
hist={}
for c in cache.values():
    k=c.get('density','unknown');hist[k]=hist.get(k,0)+1
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'width':W,'finite_horizon':H,'chunk_size':chunk,'chunks':chunks,
     'width20_dependency':'exhaustive-traps.json','new_representatives':representatives,
     'density_histogram_including_width20':hist,'best_actual':best,
     'independent_full_row_controls':controls,'stop':stop,'elapsed_seconds':time.monotonic()-start,
     'scope':'Only chunks explicitly marked full_horizon_checked are exhaustive. All-time driver and cycle certificates remain unformalized. No universal absence claim.'}
(root/'width24-traps.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['density_histogram_including_width20','stop','elapsed_seconds']}))
