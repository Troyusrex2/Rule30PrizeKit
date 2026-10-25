"""Look for a uniquely shifted nonlinear monomial in the exact F4 rule."""
from pathlib import Path
import json
root=Path(__file__).resolve().parent
def four(xs):
    for _ in range(4):xs=[xs[i]^(xs[i+1]|xs[i+2]) for i in range(len(xs)-2)]
    return xs[0]
truth=[four([(v>>i)&1 for i in range(9)]) for v in range(512)]
coeff=truth[:]
for i in range(9):
    for mask in range(512):
        if mask>>i&1:coeff[mask]^=coeff[mask^(1<<i)]
terms=[tuple(i for i in range(9) if mask>>i&1) for mask,c in enumerate(coeff) if c]
groups={}
for term in terms:
    if len(term)<2:continue
    shape=tuple(i-min(term) for i in term)
    groups.setdefault(shape,[]).append(min(term))
unique=[{'shape':list(k),'offset':v[0],'degree':len(k),'span':max(k)} for k,v in groups.items() if len(v)==1]
unique.sort(key=lambda x:(x['degree'],-x['span'],x['shape']))
replayed=0
for word in range(512):
    value=0
    for term in terms:
        value^=int(all(word>>i&1 for i in term))
    assert value==truth[word];replayed+=1
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'ANF_terms':[list(t) for t in terms],'unique_nonlinear_shapes':unique,
     'truth_table_replayed':replayed,
     'scope':'Exact local F4 algebra; a unique nonlinear shape can obstruct arbitrary position-dependent one-cell weights. No such uniform theorem is claimed here.'}
(root/'four-step-anf.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'terms':len(terms),'unique_shapes':len(unique),'smallest':unique[:8],'truth_table_replayed':replayed}),flush=True)
