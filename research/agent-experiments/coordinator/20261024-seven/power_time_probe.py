"""Quickly falsify a tempting empty-right self-similarity pattern."""
from core import save
from empty_right_absorption import step

points={(1<<k)-1 for k in range(1,17)};x=0;records=[]
for t in range(max(points)):
    x=step(x,t)
    if t+1 in points:
        expected=1<<t
        records.append({'time':t+1,'state_bit_length':x.bit_length(),'black_cells':x.bit_count(),
            'single_front_black_hypothesis':x==expected})
out={'initial_right':0,'records':records,'all_power_time_returns':all(r['single_front_black_hypothesis'] for r in records),
     'Lean_verified':False,'full_problem_solved':False}
save('power-time-probe.json',out);print(out,flush=True)
