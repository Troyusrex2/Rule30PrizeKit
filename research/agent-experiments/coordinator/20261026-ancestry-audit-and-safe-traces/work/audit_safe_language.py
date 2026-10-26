"""Independent literal-cell audit of the inferred unary safety language."""
from pathlib import Path
import json
r=Path(__file__).resolve().parent
d=json.loads((r/'safe-language-machine.json').read_bytes());table=d['table'];accept=d['accept']
N=len(table)
possible=[[bool(x) for x in accept]]
for length in range(32):possible.append([any(possible[-1][table[q][x]] for x in [0,1]) for q in range(N)])
def words(w):
    stack=[(0,0,0)];out=[]
    while stack:
        q,i,value=stack.pop()
        if i==w:
            assert accept[q];out.append(value);continue
        for b in [0,1]:
            nq=table[q][b]
            if possible[w-i-1][nq]:stack.append((nq,i+1,value|(b<<i)))
    return out
def label(value,w):
    q=0
    for j in range(w):q=table[q][value>>j&1]
    return bool(accept[q])
def step(value,w):
    row=[value>>j&1 for j in range(w)]
    out=[]
    for j,x in enumerate(row):
        # Literal Rule30 mask, with the older two white cells outside.
        out.append((30>>(4*x+2*(row[j-1] if j else 0)+(row[j-2] if j>1 else 0)))&1)
    return sum(b<<j for j,b in enumerate(out))
canonical=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]]
def canon(value,w):
    q=0
    for j in range(w):q=canonical[q][value>>j&1]
    return q in [0,1,2,3,5]
all_reports=json.loads((r/'complete-safe-orbits.json').read_bytes())['reports']+json.loads((r/'safe-stress-orbits.json').read_bytes())['reports']
by_width={x['width']:x for x in all_reports}
checks=[];cell_steps=0
for w in range(1,33):
    accepted=words(w)
    assert len(accepted)==len(set(accepted))
    for value in accepted:
        v=value;previous=v>>(w-1)&1
        for _ in range(8):
            nxt=step(v,w);b=nxt>>(w-1)&1
            assert previous or b
            v=nxt;previous=b;cell_steps+=w
        assert v==value
    if w in by_width:
        report=by_width[w]
        assert len(accepted)==report['safe_words']
        assert sorted(x for x in accepted if canon(x,w))==sorted(report['safe_canonical_words'])
    if w<=12:
        seen=set();complete_safe=0
        for value in range(1<<w):
            if value in seen:continue
            orbit=[];v=value
            while v not in seen:
                seen.add(v);orbit.append(v);v=step(v,w);cell_steps+=w
            assert v==value
            safe=all((a>>(w-1)&1) or (b>>(w-1)&1) for a,b in zip(orbit,orbit[1:]+orbit[:1]))
            assert all(label(a,w)==safe for a in orbit)
            complete_safe+=len(orbit) if safe else 0
        assert complete_safe==len(accepted)
    checks.append({'width':w,'accepted_words_literal_audited':len(accepted),
                   'complete_orbit_count_crosscheck':w in by_width,'all_words_literal_checked':w<=12})
out={'passed':True,'reports':checks,'literal_cell_updates':cell_steps,
     'all_accepted_words_through_32_return_after_eight':True,
     'all_words_through_12_checked_by_literal_rule_table':True,
     'width32_all_words_from_independent_numba_orbit_count':2**32,
     'width32_safe_words':by_width[32]['safe_words'],'Lean_verified':False,
     'uniform_classification_proved':False,'full_problem_solved':False}
(r/'safe-language-independent-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='reports'}))
