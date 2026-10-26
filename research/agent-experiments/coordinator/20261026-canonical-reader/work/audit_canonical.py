"""Independent literal language, Rule 30 truth-table, and witness controls."""
from pathlib import Path
import json,time,itertools
r=Path(__file__).resolve().parent;start=time.monotonic()
j=json.loads((r/'canonical-audit.json').read_bytes());C=j['canonical_transitions'];CA=set(j['canonical_accepting'])
d=json.loads((r/'learned-reader.json').read_bytes())['dfa'];T=d['transitions'];A=set(d['accepting'])
S=[[tuple(p) for p in ss] for ss in j['coverage']['states']];E=j['coverage']['edges']
def language(xs):
    i=next((i for i,x in enumerate(xs) if x),len(xs))
    return i>=len(xs)-2 or (i+3<len(xs) and xs[i+1]==xs[i+2])
def accepted(xs):
    q=0
    for x in xs:q=C[q][x]
    return q in CA
def relation(xs,ys):
    q=0
    for x,y in zip(xs,ys,strict=True):q=T[q][2*x+y]
    return q in A
def literal_step(xs):
    return [(30>>(4*x+2*(xs[i-1] if i else 0)+(xs[i-2] if i>=2 else 0)))&1 for i,x in enumerate(xs)]
def witness(xs):
    path=[0]
    for x in xs:path.append(E[path[-1]][x])
    q=next(p for p in S[path[-1]] if p[0] in A and p[1] in CA);ys=[]
    for i in range(len(xs)-1,-1,-1):
        p,y=next((p,y) for p in S[path[i]] for y in range(2) if (T[p[0]][2*xs[i]+y],C[p[1]][y])==q)
        ys.append(y);q=p
    assert q==(0,0)
    return ys[::-1]
word_checks=pair_checks=step_checks=0;counts=[]
for n in range(15):
    canonical=[]
    for z in range(1<<n):
        xs=[(z>>i)&1 for i in range(n)];direct=language(xs)
        assert accepted(xs)==direct
        ys=witness(xs);assert relation(xs,ys) and language(ys)
        assert language(literal_step(xs))==direct
        word_checks+=1;step_checks+=n
        if direct:canonical.append(xs)
    assert len(canonical)==(1<<(n-1) if n>=3 else 1<<n)
    counts.append({'width':n,'canonical_words':len(canonical)})
    if n<=8:
        for xs,ys in itertools.product(canonical,repeat=2):
            assert relation(xs,ys)==(xs==ys);pair_checks+=1
out={'passed':True,'all_words_max_width':14,'all_canonical_pairs_max_width':8,
     'word_witness_language_checks':word_checks,'literal_rule30_cells':step_checks,
     'canonical_pair_checks':pair_checks,'counts':counts,'seconds':round(time.monotonic()-start,3),
     'Lean_verified':False,'full_problem_solved':False}
(r/'canonical-independent-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
