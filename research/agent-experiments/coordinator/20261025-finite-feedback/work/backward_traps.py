"""Condition exact finite preimages on an official trap, not a guessed free word."""
from pathlib import Path
from fractions import Fraction
import itertools,json,random,time
import feedback_core as core
root=Path(__file__).resolve().parent;start=time.monotonic()
rng=random.Random(301709)
def counts(y):
    M=len(y);dp=[[1]*4 for _ in range(M+1)]
    for i in range(M-1,-1,-1):
        for a,b in itertools.product(range(2),repeat=2):
            dp[i][2*a+b]=sum(dp[i+1][2*b+c] for c in range(2) if a^(b|c)==y[i])
    return dp
def weighted(choices):
    total=sum(w for _,w in choices)
    if not total:return None
    z=rng.randrange(total)
    for x,w in choices:
        if z<w:return x
        z-=w
    raise AssertionError('weights')
def preimage(y,boundary,prefer=None):
    dp=counts(y);M=len(y)
    choices=[(b,dp[0][2*boundary+b]) for b in range(2)]
    if prefer is not None and choices[prefer][1]:b=prefer
    else:b=weighted(choices)
    if b is None:return None
    old=[b];a=boundary
    for i in range(M):
        c=weighted([(c,dp[i+1][2*b+c]) for c in range(2) if a^(b|c)==y[i]])
        assert c is not None
        old.append(c);a,b=b,c
    assert all((([boundary]+old)[i]^(old[i]|old[i+1]))==y[i] for i in range(M))
    return old
control_words=control_preimages=0
for M in range(1,7):
    for y in itertools.product(range(2),repeat=M):
        dp=counts(y)
        for boundary in range(2):
            exact=[old for old in itertools.product(range(2),repeat=M+1)
                   if all((([boundary]+list(old))[i]^(old[i]|old[i+1]))==y[i] for i in range(M))]
            assert sum(dp[0][2*boundary+b] for b in range(2))==len(exact)
            sample=preimage(y,boundary)
            assert (sample is None)==(not exact)
            if sample is not None:assert tuple(sample) in exact
            control_words+=1;control_preimages+=len(exact)
records=[];cache={};best=None;failures={};stop=None
with (root/'backward-traps.partial.jsonl').open('w',encoding='utf-8') as log:
    for T in [15,16,31,32,63,64,95,96,127,128]:
        for trial in range(100):
            if time.monotonic()-start>230:stop='internal_time_budget';break
            phase=rng.choice([q for q in range(4) if core.table[3][q]==int(T%2==0)])
            wall=rng.choice(sorted(core.wallsets[phase]))
            target=[core.table[(3+p)%7][phase] for p in range(1,7)]+[wall>>i&1 for i in range(13)]
            current=target[:];failure=None
            policy=['uniform','prefer_free_zero','prefer_free_one','alternating'][trial%4]
            for depth in range(T):
                oldtime=T-1-depth
                preference=None
                if oldtime%2:
                    if policy=='prefer_free_zero':preference=1
                    elif policy=='prefer_free_one':preference=0
                    elif policy=='alternating':preference=1^(oldtime//2%2)
                old=preimage(current,int(oldtime%2==0),preference)
                if old is None:failure=depth;break
                current=old
            if failure is not None:
                failures[str(T)]=failures.get(str(T),0)+1
                continue
            code=sum(b<<(i+1) for i,b in enumerate(current))
            row=code|1
            for t in range(T):row=core.step(row,t)
            assert [row>>(i+1)&1 for i in range(19)]==target
            trap=core.trapped(code,cap=T)
            assert trap is not None
            key=(tuple(trap['free_prefix']),trap['tail_first'])
            if key not in cache:cache[key]=core.spatial_cycle(*key)
            cycle=cache[key]
            n=max(256,len(key[0])+64)
            actual=core.free_stream(code,n)
            expected=list(key[0])+[key[1]^(j%2) for j in range(n-len(key[0]))]
            assert actual==expected
            rec={'T':T,'trial':trial,'policy':policy,'initial_right_hex':hex(code),
                 'initial_max_position':code.bit_length()-1,'root_phase':phase,'root_wall':wall,
                 'earliest_detected_trap':trap,'spatial_cycle':cycle}
            records.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
            if 'period' in cycle and (best is None or Fraction(cycle['density'])<Fraction(best['spatial_cycle']['density'])):
                best=rec;print(json.dumps({'new_actual_minimum':rec}),flush=True)
            if cycle.get('C3_positive_drift'):stop='actual_finite_right_C3_counterexample_candidate';break
        print(json.dumps({'T_done':T,'successes':sum(r['T']==T for r in records),'failed_restarts':failures.get(str(T),0),
                          'unique_streams_total':len(cache)}),flush=True)
        if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'controls':{'exhaustive_target_boundary_words':control_words,'exhaustive_preimages_counted':control_preimages},
     'requested_depths':[15,16,31,32,63,64,95,96,127,128],'requested_restarts_each':100,
     'records':records,'failed_restarts':failures,'unique_complete_streams':len(cache),
     'exact_cycles':sum('period' in c for c in cache.values()),'best_actual':best,'stop':stop,
     'elapsed_seconds':time.monotonic()-start,
     'scope':'Each successful restart is an actual finite R, checked by complete forward evolution to a catalog trap. Complete driver and spatial cycle remain candidate certificates until their bridge is kernel checked.'}
(root/'backward-traps.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'successes':len(records),'unique_streams':len(cache),'exact_cycles':out['exact_cycles'],'stop':stop,'elapsed_seconds':out['elapsed_seconds']}))
