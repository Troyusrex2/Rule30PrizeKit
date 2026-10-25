"""Falsify the generic Golden C4 floor with complete cycles, not an observed word."""
from pathlib import Path
from fractions import Fraction
import hashlib,json,random,time
import feedback_core as core
root=Path(__file__).resolve().parent;start=time.monotonic();rng=random.Random(301745)
forbidden=['00','11111','010110','1011010']
def allowed(s):return not any(w in s for w in forbidden)
def sample(m):
    s=''
    for _ in range(m):
        choices=[b for b in '01' if allowed((s+b)[-8:])]
        assert choices
        s+=rng.choice(choices)
    choices=[b for b in '01' if allowed((s[-8:]+''.join(str(int(b)^(i%2)) for i in range(12))))]
    if not choices:return None
    return list(map(int,s)),int(rng.choice(choices))
best=None;records=[];hist={};rejected=0;stop=None
with (root/'golden-density.partial.jsonl').open('w',encoding='utf-8') as log:
    for m in [64,128,256,512,1024]:
        for trial in range(2500):
            if time.monotonic()-start>230:stop='internal_time_budget';break
            value=sample(m)
            if value is None:rejected+=1;continue
            prefix,first=value
            assert allowed(''.join(map(str,prefix))+''.join(str(first^(i%2)) for i in range(16)))
            cycle=core.spatial_cycle(prefix,first,cap=30000)
            key=cycle.get('density','unknown');hist[key]=hist.get(key,0)+1
            rec={'m':m,'trial':trial,'prefix':prefix,'tail_first':first,'cycle':cycle}
            if 'period' in cycle and (best is None or Fraction(cycle['density'])<Fraction(best['cycle']['density'])):
                best=rec;records.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
                print(json.dumps({'minimum':{k:cycle[k] for k in ['entry_depth','period','black','density']},'m':m,'trial':trial}),flush=True)
            if 'period' in cycle and 3*cycle['period']>16*cycle['black']:
                stop='generic_Golden_C4_counterexample_candidate';break
        print(json.dumps({'m_done':m,'samples':sum(hist.values()),'min_density':best['cycle']['density'] if best else None,'elapsed_seconds':time.monotonic()-start}),flush=True)
        if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'rng_seed':301745,'forbidden_words':forbidden,'history_minima':records,'best':best,
     'density_histogram':hist,'samples':sum(hist.values()),'rejected_tail_seams':rejected,
     'stop':stop,'elapsed_seconds':time.monotonic()-start,
     'scope':'Arbitrary Golden drivers satisfying four finite necessary word constraints, NOT actual finite R. A generic C4 failure would not refute actual coupled C4 or solve P1.'}
(root/'golden-density.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['samples','stop','elapsed_seconds']}))
