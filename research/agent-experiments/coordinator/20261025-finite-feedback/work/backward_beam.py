"""Branch over actual preimages; retain complete finite words, never ghost drivers."""
from pathlib import Path
from fractions import Fraction
import itertools,json,random,time
import feedback_core as core
root=Path(__file__).resolve().parent
start=time.monotonic();rng=random.Random(301725)

def all_preimages(y,boundary,cap=256):
    M=len(y);dp=[[1]*4 for _ in range(M+1)]
    for i in range(M-1,-1,-1):
        for a,b in itertools.product(range(2),repeat=2):
            dp[i][2*a+b]=sum(dp[i+1][2*b+c] for c in range(2) if a^(b|c)==y[i])
    total=sum(dp[0][2*boundary+b] for b in range(2))
    ranks=range(total) if total<=cap else sorted(rng.sample(range(total),cap))
    out=[]
    for rank in ranks:
        a=boundary;b=0
        if rank>=dp[0][2*a]:rank-=dp[0][2*a];b=1
        word=[b]
        for i in range(M):
            for c in range(2):
                if a^(b|c)!=y[i]:continue
                count=dp[i+1][2*b+c]
                if rank<count:break
                rank-=count
            word.append(c);a,b=b,c
        out.append(tuple(word))
    assert len(set(out))==len(out)
    return total,out

# Exhaustive independent check, including fixed-boundary Garden-of-Eden words.
controls=0
for M in range(1,7):
    for y in itertools.product(range(2),repeat=M):
        for b in range(2):
            total,found=all_preimages(y,b)
            exact={x for x in itertools.product(range(2),repeat=M+1)
                   if all((([b]+list(x))[i]^(x[i]|x[i+1]))==y[i] for i in range(M))}
            assert total==len(exact) and set(found)==exact
            controls+=1

known=json.loads((root/'trap-cycles.json').read_text())['best_actual']
known_code=int(known['initial_right_hex'],16)
known_T=known['trap']['time']
rows=[known_code|1]
for t in range(known_T):rows.append(core.step(rows[-1],t))
known_root=tuple(rows[-1]>>(i+1)&1 for i in range(19))
known_path_controls=0
for depth in range(known_T):
    t=known_T-depth
    target=tuple(rows[t]>>(i+1)&1 for i in range(19+depth))
    predecessor=tuple(rows[t-1]>>(i+1)&1 for i in range(20+depth))
    total,found=all_preimages(target,int((t-1)%2==0),cap=100000)
    assert predecessor in found
    known_path_controls+=1

records=[];cache={};levels=[];best=None;stop=None
with (root/'backward-beam.partial.jsonl').open('w',encoding='utf-8') as log:
    # Odd/even terminal times. Known W2 root is included in the odd-time basin.
    for T in [31,32,63,64,95,96]:
        roots=[]
        for phase in range(4):
            if core.table[3][phase]!=int(T%2==0):continue
            for wall in sorted(core.wallsets[phase]):
                target=tuple([core.table[(3+p)%7][phase] for p in range(1,7)]+
                             [wall>>i&1 for i in range(13)])
                roots.append(target)
        beam=list(dict.fromkeys(roots));rootset=set(beam)
        for depth in range(T):
            if time.monotonic()-start>230:stop='internal_time_budget';break
            oldtime=T-1-depth;children=set();total_edges=0;sampled=0
            for y in beam:
                total,found=all_preimages(y,int(oldtime%2==0),cap=64)
                total_edges+=total;sampled+=len(found);children.update(found)
            population=len(children)
            beam=sorted(children)
            if len(beam)>384:beam=rng.sample(beam,384)
            level={'T':T,'depth':depth+1,'population_before_beam_cap':population,
                   'retained':len(beam),'possible_edges':total_edges,'sampled_edges':sampled}
            levels.append(level)
            if not beam:break
        if stop:break
        if depth+1==T:
            for word in beam:
                if time.monotonic()-start>230:stop='internal_time_budget';break
                code=sum(b<<(i+1) for i,b in enumerate(word));row=code|1
                for t in range(T):row=core.step(row,t)
                assert tuple(row>>(i+1)&1 for i in range(19)) in rootset
                trap=core.trapped(code,cap=T);assert trap is not None
                key=(tuple(trap['free_prefix']),trap['tail_first'])
                if key not in cache:cache[key]=core.spatial_cycle(*key)
                cycle=cache[key];n=max(256,len(key[0])+64)
                assert core.free_stream(code,n)==list(key[0])+[key[1]^(j%2) for j in range(n-len(key[0]))]
                rec={'T':T,'initial_right_hex':hex(code),'trap':trap,'spatial_cycle':cycle}
                records.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
                if 'period' in cycle and (best is None or Fraction(cycle['density'])<Fraction(best['spatial_cycle']['density'])):
                    best=rec;print(json.dumps({'new_actual_minimum':rec}),flush=True)
                if cycle.get('C3_positive_drift'):stop='actual_finite_right_C3_counterexample_candidate';break
        print(json.dumps({'T_done':T,'last_depth':depth+1,'retained':len(beam),
                          'successes':len(records),'unique_streams':len(cache)}),flush=True)
        if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'seed':301725,'beam_cap':384,'preimages_per_node_cap':64,
     'controls':{'exhaustive_words':controls,'known_actual_ancestry':known_path_controls},
     'records':records,'levels':levels,'unique_streams':len(cache),'best_actual':best,
     'stop':stop,'elapsed_seconds':time.monotonic()-start,
     'scope':'Complete finite-R forward validation; exact sampled spatial cycles are not kernel-certified. Beam truncation is heuristic and no absence proof.'}
(root/'backward-beam.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'successes':len(records),'unique_streams':len(cache),'stop':stop,'elapsed_seconds':out['elapsed_seconds']}))
