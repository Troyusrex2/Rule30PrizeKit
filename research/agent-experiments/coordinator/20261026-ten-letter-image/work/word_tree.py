"""Produce explicit local-case trees, separate from the SMT result."""
from pathlib import Path
import itertools,json
ROOT=Path(__file__).resolve().parent
word=[int(x) for x in '1010111010']
table=[a for a in itertools.product(range(2),repeat=4) if a[0]==(a[1]^(a[2]|a[3]))]

def search(start_odd):
    height=2*len(word)-(1 if start_odd else 0)
    known={(t,0):int(t%2==int(start_odd)) for t in range(height)}
    offset=0 if start_odd else 1
    known.update({(2*s+offset,1):1-v for s,v in enumerate(word)})
    initial=[{'cell':list(k),'value':v} for k,v in known.items()]
    constraints=[[(t+1,p),(t,p-1),(t,p),(t,p+1)]
                 for t in range(height-1) for p in range(1,height-t)]
    nodes=0
    def dfs(known):
        nonlocal nodes
        nodes+=1;assert nodes<=10000
        steps=[]
        while True:
            changed=False;open_relations=[]
            for cells in constraints:
                prior={k:known[k] for k in cells if k in known}
                allowed=[a for a in table if all(k not in prior or a[i]==prior[k] for i,k in enumerate(cells))]
                if not allowed:
                    return {'steps':steps,'conflict':[list(k) for k in cells]}
                for i,k in enumerate(cells):
                    if k not in known and len({a[i] for a in allowed})==1:
                        value=allowed[0][i]
                        steps.append({'cell':list(k),'value':value,'relation':[list(q) for q in cells],
                                      'premises':[{'cell':list(q),'value':v} for q,v in prior.items()]})
                        known[k]=value;changed=True
                if len(allowed)>1:
                    open_relations.append((len(allowed),len(prior),cells))
            if not changed:break
        if not open_relations:
            return {'steps':steps,'sat':True}
        candidates={}
        for n,_,cells in open_relations:
            for k in cells:
                if k not in known:candidates[k]=candidates.get(k,0)+1/n
        k=max(candidates,key=lambda k:(candidates[k],-k[0],-k[1]))
        branches=[]
        for v in [0,1]:
            branch=dfs({**known,k:v});branches.append(branch)
            if branch.get('sat'):return {'steps':steps,'sat':True,'witness':branch}
        return {'steps':steps,'split':list(k),'branches':branches}
    tree=dfs(dict(known))
    return {'start_odd':start_odd,'word':word,'height':height,'initial':initial,'tree':tree,
            'nodes':nodes,'unsat':not tree.get('sat'),'Lean_verified':False}
for start_odd in [True,False]:
    out=search(start_odd)
    (ROOT/('word-tree-'+('odd' if start_odd else 'even')+'.json')).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['initial','tree']}),flush=True)
