"""Falsify a candidate: four distinct histories forming a permanent XOR rectangle."""
from pathlib import Path
from collections import defaultdict
import json,time

root=Path(__file__).resolve().parent

def step(a,width=None):
    if width is None:return a ^ ((a<<1)|(a<<2))
    mask=(1<<width)-1
    r1=((a<<1)|(a>>(width-1)))&mask
    r2=((a<<2)|(a>>(width-2)))&mask
    return a ^ (r1|r2)

def run(width,ring=False):
    n=1<<width;states=list(range(n))
    groups=defaultdict(list)
    for a in range(n):
        for b in range(a+1,n):groups[a^b].append((a,b))
    groups=[g for g in groups.values() if len(g)>1]
    records=[];last_witness=None;stable=False
    for t in range(129):
        count=sum(len(g)*(len(g)-1)//2 for g in groups)
        assert count%3==0
        records.append({'time':t,'XOR_rectangles':count//3,'nontrivial_pair_classes':len(groups)})
        if not groups:break
        g=groups[0];last_witness=(*g[0],*g[1])
        states=[step(s,width if ring else None) for s in states]
        smaller=[]
        for g in groups:
            buckets=defaultdict(list)
            for a,b in g:buckets[states[a]^states[b]].append((a,b))
            smaller.extend(v for v in buckets.values() if len(v)>1)
        if ring and smaller==groups:
            stable=True
            break
        groups=smaller
    result={'width':width,'periodic_ring':ring,'records':records,
            'all_distinct_rectangles_killed':not groups,'stable_ring_partition':stable,
            'finite_only':not ring or not stable}
    if stable:
        s=last_witness;seen={};history=[]
        for t in range(10000):
            assert s[0]^s[1]^s[2]^s[3]==0
            if s in seen:
                result['ring_counterexample']={'initial_four':last_witness,
                    'transient':seen[s],'cycle_length':t-seen[s],'states':history}
                break
            seen[s]=t;history.append(s)
            s=tuple(step(a,width) for a in s)
        assert 'ring_counterexample' in result
    return result

started=time.monotonic()
finite=[run(w) for w in range(2,11)]
rings=[run(w,True) for w in range(3,9)]
result={'candidate':'No four distinct finite Rule30 histories have XOR zero at all times.',
        'candidate_proved':False,'candidate_refuted_by_finite_starts':False,
        'finite_start_controls':finite,'periodic_ring_controls':rings,
        'seconds':time.monotonic()-started,'full_problem_solved':False}
(root/'affine-history.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'finite':[(r['width'],r['records'][-1]) for r in finite],
                  'rings':[(r['width'],r.get('ring_counterexample',{}).get('initial_four')) for r in rings],
                  'seconds':result['seconds']}))
