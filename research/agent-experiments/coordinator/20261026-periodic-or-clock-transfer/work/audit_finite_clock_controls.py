"""Independent finite-white literal Rule30 controls; not proof premises."""
from pathlib import Path
import json

root = Path(__file__).resolve().parent

def step(state, width):
    bits = [(state >> j) & 1 for j in range(width)]
    return sum(((30 >> (4 * bits[j] + 2 * (bits[j-1] if j else 0)
                        + (bits[j-2] if j >= 2 else 0))) & 1) << j for j in range(width))

def periodic(profile, shift):
    return all(profile[(t+shift) % len(profile)] == x for t,x in enumerate(profile))

def anti(profile, shift):
    return all(profile[(t+shift) % len(profile)] != x for t,x in enumerate(profile))

reports=[]
odd_control=None
dropped_older_control=None
for width in range(7,13):
    visited=set();checks=orbits=0;clock_counts={}
    for seed in range(1 << width):
        if seed in visited: continue
        orbit=[];state=seed
        while state not in visited:
            visited.add(state);orbit.append(state)
            nxt=step(state,width)
            assert nxt == (state ^ ((state<<1)|(state<<2))) & ((1<<width)-1)
            state=nxt
        assert state==seed
        orbits+=1
        profiles=[[(x>>j)&1 for x in orbit] for j in range(width)]
        for j in range(width-6):
            l,k,h,g,x=profiles[j+2:j+7]
            out=[a|b for a,b in zip(g,h)]
            R=1
            while R <= len(orbit):
                if anti(k,R):
                    if periodic(l,R):
                        if R % 2 == 0:
                            assert not periodic(out,R)
                            assert not periodic(x,R)
                            checks+=1;clock_counts[R]=clock_counts.get(R,0)+1
                        elif odd_control is None and periodic(out,R):
                            odd_control={'width':width,'seed':seed,'j':j,'R':R,'orbit':orbit,
                                         'older_periodic':True,'OR_periodic':True}
                    elif dropped_older_control is None and R%2==0 and periodic(out,R):
                        dropped_older_control={'width':width,'seed':seed,'j':j,'R':R,'orbit':orbit,
                                               'older_periodic':False,'OR_periodic':True}
                R*=2
    reports.append({'width':width,'all_words':len(visited),'complete_orbits':orbits,
                    'premise_instances_checked':checks,'source_half_clocks':clock_counts})
assert odd_control is not None
result={'passed':True,'reports':reports,'odd_half_clock_counterexample':odd_control,
        'dropping_older_period_control':dropped_older_control,
        'source_update':'literal rule table with two white older boundary cells',
        'scope':'finite independent controls, not used as proof premises'}
(root/'finite-clock-controls.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':True,'words':sum(x['all_words'] for x in reports),
                  'premise_instances':sum(x['premise_instances_checked'] for x in reports),
                  'odd_R_counterexample':{k:v for k,v in odd_control.items() if k!='orbit'},
                  'dropping_older_period_found':dropped_older_control is not None}))
