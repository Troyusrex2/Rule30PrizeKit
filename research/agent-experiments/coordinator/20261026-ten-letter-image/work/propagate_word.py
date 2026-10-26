"""Exact local propagation; each deduction uses the 16-value Rule30 table."""
from pathlib import Path
import itertools,json
ROOT=Path(__file__).resolve().parent
word=[int(x) for x in '1010111010'];height=2*len(word)-1
known={(t,0):int(t%2==1) for t in range(height)}
known.update({(2*s,1):1-v for s,v in enumerate(word)})
initial=[{'cell':list(k),'value':v} for k,v in known.items()]
steps=[];contradiction=None
constraints=[[(t+1,p),(t,p-1),(t,p),(t,p+1)]
             for t in range(height-1) for p in range(1,height-t)]
table=[(n,a,b,c) for n,a,b,c in itertools.product(range(2),repeat=4) if n==(a^(b|c))]
while True:
    changed=False
    for cells in constraints:
        prior={k:known[k] for k in cells if k in known}
        allowed=[a for a in table if all(k not in prior or a[i]==prior[k] for i,k in enumerate(cells))]
        if not allowed:
            contradiction={'relation':[list(k) for k in cells],'premises':[{'cell':list(k),'value':v} for k,v in prior.items()]}
            break
        for i,k in enumerate(cells):
            if k not in known and len({a[i] for a in allowed})==1:
                value=allowed[0][i]
                steps.append({'cell':list(k),'value':value,'relation':[list(q) for q in cells],
                              'premises':[{'cell':list(q),'value':v} for q,v in prior.items()]})
                known[k]=value;changed=True
    if contradiction or not changed:break
out={'word':word,'height':height,'initial':initial,'steps':steps,'contradiction':contradiction,
     'known_cells':len(known),'unresolved_is_not_sat':True,'Lean_verified':False}
(ROOT/'local-propagation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'steps':len(steps),'contradiction':contradiction,'Lean_verified':False}))
