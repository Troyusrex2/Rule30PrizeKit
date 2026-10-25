"""Finite guided predecessor search, with known actual ancestries retained."""
from pathlib import Path
from fractions import Fraction
import json,random,time
import feedback_core as core
from preimage_core import all_preimages
root=Path(__file__).resolve().parent;start=time.monotonic();rng=random.Random(301735)
records=[];levels=[];cache={};best=None;stop=None
with (root/'guided-preimages.partial.jsonl').open('w',encoding='utf-8') as log:
    for seedcode,T in [(0x72270,31),(0x72270,47),(0x888,59),(0x72270,95),(0x888,127)]:
        rows=[seedcode|1]
        for t in range(T):rows.append(core.step(rows[-1],t))
        trap_at_end=core.trapped(seedcode,cap=T)
        if trap_at_end is None:continue
        target=tuple(rows[-1]>>(i+1)&1 for i in range(19))
        beam=[target]
        for depth in range(T):
            if time.monotonic()-start>230:stop='internal_time_budget';break
            oldtime=T-1-depth;children=set()
            for y in beam:
                _,found=all_preimages(y,int(oldtime%2==0),cap=64)
                children.update(found)
            guide=tuple(rows[oldtime]>>(i+1)&1 for i in range(20+depth))
            # This injection has its own complete, independently forward-checked ancestry.
            children.add(guide)
            population=len(children)
            ordered=sorted(children,key=lambda x:(sum(a!=b for a,b in zip(x,guide)),x))
            if len(ordered)>512:
                beam=ordered[:128]+rng.sample(ordered[128:],384)
            else:beam=ordered
            assert guide in beam
            levels.append({'seed':hex(seedcode),'T':T,'depth':depth+1,
                           'population':population,'retained':len(beam)})
        if stop:break
        rng.shuffle(beam)
        for word in beam:
            if time.monotonic()-start>230:stop='internal_time_budget';break
            code=sum(b<<(i+1) for i,b in enumerate(word));row=code|1
            for t in range(T):row=core.step(row,t)
            assert tuple(row>>(i+1)&1 for i in range(19))==target
            trap=core.trapped(code,cap=T);assert trap is not None
            key=(tuple(trap['free_prefix']),trap['tail_first'])
            if key not in cache:cache[key]=core.spatial_cycle(*key)
            cycle=cache[key];n=max(256,len(key[0])+64)
            assert core.free_stream(code,n)==list(key[0])+[key[1]^(j%2) for j in range(n-len(key[0]))]
            rec={'T':T,'guide_seed_hex':hex(seedcode),'initial_right_hex':hex(code),
                 'trap':trap,'spatial_cycle':cycle}
            records.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
            if 'period' in cycle and (best is None or Fraction(cycle['density'])<Fraction(best['spatial_cycle']['density'])):
                best=rec;print(json.dumps({'new_actual_minimum':rec}),flush=True)
            if cycle.get('C3_positive_drift'):stop='actual_finite_right_C3_counterexample_candidate';break
        print(json.dumps({'T_done':T,'seed':hex(seedcode),'successes':len(records),
                          'unique_streams':len(cache)}),flush=True)
        if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'rng_seed':301735,'beam_cap':512,'preimages_per_node_cap':64,
     'records':records,'levels':levels,'unique_streams':len(cache),'best_actual':best,
     'stop':stop,'elapsed_seconds':time.monotonic()-start,
     'scope':'Known rows injected only with independently valid actual ancestry. All resulting initial codes forward checked. Spatial cycles remain computational certificates, not Lean theorems.'}
(root/'guided-preimages.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'successes':len(records),'unique_streams':len(cache),'stop':stop,'elapsed_seconds':out['elapsed_seconds']}))
