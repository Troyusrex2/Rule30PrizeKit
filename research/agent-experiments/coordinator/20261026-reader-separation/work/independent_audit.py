from pathlib import Path
from itertools import product
import json
root=Path(__file__).resolve().parent
dfa=json.loads((root/'learned-reader.json').read_bytes())['dfa']
phase=[0,1,2,3,5,4,7,6,10,11,8,9,12,14,13,15,16]
def run(w):
    q=dfa['start']
    for s in w:q=dfa['transitions'][q][s]
    return q
def literal(row):
    return [row[j] ^ ((row[j-1] if j>=1 else 0)|(row[j-2] if j>=2 else 0)) for j in range(len(row))]
def step(w):
    a=literal([s>>1 for s in w]);b=literal([s&1 for s in w])
    return [(x<<1)|y for x,y in zip(a,b)]
tested=0;sink_two_equal=0
for n in range(7):
    for w in product(range(4),repeat=n):
        q=run(w);v=step(w);q1=run(v)
        assert q1==phase[q] and run(step(v))==q
        assert (q==15)==(q1==15)
        same0=not w or w[-1] in (0,3)
        same1=not v or v[-1] in (0,3)
        if q!=15:assert (q in dfa['accepting'])==(same0 and same1)
        elif same0 and same1:sink_two_equal+=1
        tested+=1
assert sink_two_equal>0
def profile(word,n,j):
    row=[(word>>k)&1 for k in range(n)];P=1<<(n-1);x=0
    for t in range(P):
        x|=row[j]<<t;row=literal(row)
    assert row==[(word>>k)&1 for k in range(n)]
    return x,P
def difference(x,P):
    return x ^ ((x>>1)|((x&1)<<(P-1)))
def scalar_degree(x,P):
    if not x:return -1
    d=0
    while x:
        x=difference(x,P);d+=1
        assert d<=P
    return d-1
controls=[]
for word,n,js,expected in [(545,12,[9,10,11],[29,31,31]),(3361,14,[11,12,13],[31,30,28])]:
    ds=[scalar_degree(*profile(word,n,j)) for j in js]
    assert ds==expected
    controls.append({'initial':word,'width':n,'depths':js,'degrees':ds,'literal_period_verified':True})
a,b,n=24576,16153,16
word=[(((a>>j)&1)<<1)|((b>>j)&1) for j in range(n)]
assert run(word)==15
first=None
for t in range(46):
    if word[-1] in (1,2):first=t;break
    word=step(word)
assert first==44
late=json.loads((root/'late-separation.json').read_bytes())['witness']
assert late['status']=='different' and late['width']==22 and late['first_difference_time']==72
a,b,n=late['a_initial'],late['b_initial'],late['width']
word=[(((a>>j)&1)<<1)|((b>>j)&1) for j in range(n)]
assert run(word)==15
same=[]
for t in range(73):
    same.append(word[-1] in (0,3));word=step(word)
assert same==[True]*72+[False] and 72>3*n
bad=phase.copy();bad[4]=4
assert any(run(step(w))!=bad[run(w)] for w in product(range(4),repeat=2))
out={'passed':True,'factor_controls':tested,'sink_words_equal_for_first_two_times':sink_two_equal,
     'wrong_phase_rejected':True,'literal_degree_counterexamples':controls,
     'sink_delay_control':{'width':16,'first_difference_time':first},
     'three_width_bound_falsified':{'width':n,'first_difference_time':72,'literal_all_73_steps_checked':True},
     'Lean_verified':False,'sink_separation_proved':False,'full_problem_solved':False}
(root/'independent-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
