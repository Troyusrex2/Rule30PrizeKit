"""Measure exactly where the finite example stops meeting observer premises."""
from pathlib import Path
import json,runpy
ROOT=Path(__file__).resolve().parent
independent=runpy.run_path(str(ROOT/'independent_sensor_check.py'))
physical=independent['physical'];auxiliary=independent['auxiliary'];rows=independent['rows']
U,V=256,237
while len(rows)<=U+65:
    rows.append(physical(rows[-1]))
h=rows[U]^rows[V]^{U}
first_center=None;first_wedge=None
for t in range(65):
    delta=rows[U+t]^rows[V+t]
    if first_center is None and 0 in h:first_center=t
    if first_wedge is None:
        bad=next((p for p in range(-U-t-1,U+t+1)
                  if (((p+1 in delta) and (p in h)) != ((p in delta) and (p+1 in h)))),None)
        if bad is not None:first_wedge={'t':t,'p':bad}
    h=auxiliary(rows[U+t],rows[V+t],h)
assert first_center is not None and first_center>6
assert first_wedge is not None and first_wedge['t']>6
result={'U':U,'V':V,'checked_through':64,'first_nonzero_center':first_center,
        'first_W_failure':first_wedge,'all_time_D_by_construction':True,
        'all_time_W':False,'all_time_invisible':False,'full_problem_solved':False}
(ROOT/'beyond-window.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
