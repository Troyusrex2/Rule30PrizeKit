"""Exact travelling fronts in periodic Rule30 controls, not the finite seed."""
from fractions import Fraction
from pathlib import Path
import json
table=['0011','0110','1101','0101','0011','0001','0001']
def field(t,x):return int(table[x%7][t%4])
assert all(field(t+1,x)==(field(t,x-1)^(field(t,x)|field(t,x+1))) for t in range(4) for x in range(7))
records=[];identity=0
for dx in range(7):
    for dt in range(4):
        def D(t,x):return field(t,x)^field(t+dt,x+dx)
        if all(not D(t,x) for t in range(4) for x in range(7)):
            identity+=1;continue
        for r0 in range(-7,0):
            if not D(0,r0):continue
            r=r0;t=0;seen={};walk=[]
            while (t%4,r%7) not in seen:
                seen[t%4,r%7]=(t,r)
                nxt=next(r+1-k for k in range(7) if D(t+1,r+1-k))
                # Independent lexicographic-parent interpretation on both
                # sides of the interface, retaining left-group labels.
                for x in range(r-14,r+15):
                    if D(t+1,x):
                        parent=next(y for y in [x-1,x,x+1] if D(t,y))
                        assert (parent<=r)==(x<=nxt)
                walk.append({'time':t,'front':r,'next_front':nxt})
                t+=1;r=nxt
            first,oldr=seen[t%4,r%7];period=t-first;drift=r-oldr
            records.append({'spatial_shift':dx,'time_shift':dt,'initial_front':r0,
                            'cycle_start':first,'cycle_length':period,'cycle_displacement':drift,
                            'velocity':str(Fraction(drift,period)),
                            'center_columns_identical_all_time':all(not D(k,0) for k in range(4)),
                            'walk':walk})
out={'finite_state_computation':True,'Lean_verified':False,'identity_shift_pairs':identity,'records':records,
     'nonpositive_cycles':sum(r['cycle_displacement']<=0 for r in records),
     'scope':'Two spatially infinite periodic ether histories with coarsened left/right ancestor labels. These are not finite canonical seed comparisons or counterexamples to Problem1.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'cycles':len(records),'velocities':sorted({r['velocity'] for r in records}),
                  'nonpositive':out['nonpositive_cycles'],'first_same_center':next(r for r in records if r['center_columns_identical_all_time'])},indent=2))
