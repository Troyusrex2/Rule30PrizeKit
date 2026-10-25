"""Independent physical selected-parent replay of the root resource witness."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
def step(s):
    return {x for x in range(min(s)-1,max(s)+2) if int(x-1 in s)^(int(x in s)|int(x+1 in s))}
rows=[{0}]
for _ in range(6):rows.append(step(rows[-1]))
a,b=rows[0],rows[4];labels={x:x for x in a^b};source=min(labels)
record=[]
for t in range(3):
    points=sorted(x for x in labels if labels[x]==source)
    record.append({'time':t,'center_A':int(0 in a),'center_B':int(0 in b),
                   'least_source':source,'root_positions':points,'front':max(points)})
    if t<2:
        an,bn=step(a),step(b)
        labels={x:labels[min(y for y in [x-1,x,x+1] if y in labels)] for x in an^bn}
        a,b=an,bn
assert [r['center_A'] for r in record]==[1,1,0]==[r['center_B'] for r in record]
assert record[0]['root_positions']==[-4] and record[2]['root_positions']==[-6,-5]
data=json.loads((root/'root-gap-potential.json').read_text())
w=data['coordinatewise_nonnegative_potential_counterexample']
assert (w['T'],w['P'],w['elapsed'])==(0,4,0)
assert w['before']==[4,1,1,0,0,0,0,1,1,0,0,0]
assert w['after']==[5,2,1,0,0,0,0,4,2,0,0,0]
assert all(y>=x for x,y in zip(w['before'],w['after']))
out={'finite_only':True,'Lean_verified':False,'independent_physical_control':True,'records':record,
     'all_centers_match':True,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(root/'root-small-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
