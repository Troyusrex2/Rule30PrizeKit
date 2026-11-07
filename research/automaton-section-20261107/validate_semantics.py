"""Bounded semantic replay of the preregistered encoding, not aperiodicity evidence."""
from pathlib import Path
from itertools import product
import json,time
R=Path(__file__).resolve().parent
start=time.monotonic()
A,B,C=0,1,2
flip=(0,1,1)
nxt=((A,C),(A,C),(B,C))
def act(s,bits):
    result=[]
    for b in bits:
        result.append(b^flip[s]);s=nxt[s][b]
    return result
def dual(b,w):
    result=[]
    for s in w:
        result.append(nxt[s][b]);b^=flip[s]
    return result
def rounds(k,w):
    for _ in range(k):w=dual(0,w)
    return w
def parity(w):return sum(flip[s] for s in w)%2
def wordact(w,bits):
    for s in w:bits=act(s,bits)
    return bits
table=(0,1,1,1,1,0,0,0)
def literal_step(row):
    pos={p+d for p in row for d in (-1,0,1)}
    return {p for p in pos if table[4*(p-1 in row)+2*(p in row)+(p+1 in row)]}
row={0};code=[1]+[0]*258
records=[]
for t in range(1,129):
    row=literal_step(row);code=act(A,code)
    assert code[:2*t+3]==[int(t-j in row) for j in range(2*t+3)]
    core=rounds(t-1,[C]*t)
    assert parity(core)==int(0 in row)
    output=wordact(core,[0]*(t+3))
    assert output==[int(-k in row) for k in range(t+3)]
    drop=(t-1)//2
    assert core[:drop]==[A]*drop
    short=core[drop:]
    assert len(short)==(t+2)//2
    assert wordact(short,[0]*(t+3))==output
    records.append({'age':t,'center':int(0 in row),'minimum_positive_length':len(short)})
count=0
for length in range(7):
    for tup in product((A,B,C),repeat=length):
        w=list(tup)
        assert dual(0,dual(0,[C]+w))==[A]+dual(1,dual(1,w))
        assert dual(0,dual(0,[C,C]+w))==[A,C]+dual(0,dual(0,w))
        count+=1
def number(perms,sections):
    s=[v for pair in sections for v in pair]
    return 1+sum(3**i*v for i,v in enumerate(s))+729*sum(2**i*v for i,v in enumerate(perms))
raw=number(flip,nxt)
rename={A:2,B:1,C:0}
p=[0]*3;q=[None]*3
for old in range(3):
    new=rename[old];p[new]=flip[old];q[new]=tuple(rename[v] for v in nxt[old])
canonical=number(p,q)
assert raw==5002 and canonical==2369
assert p==[1,1,0] and q==[(1,0),(2,0),(2,0)]
out={'pass':True,'max_age':128,'dual_identity_words':count,'automaton_number':raw,
     'renamed_number':canonical,'renaming':'A->c, B->b, C->a',
     'literal_lookup_table_000_to_111':table,'records':records,'seconds':time.monotonic()-start,
     'scope':'finite semantic checks only; infinite statements use Lean kernel proofs'}
(R/'semantic-validation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ('pass','max_age','dual_identity_words','automaton_number','renamed_number','seconds')}))
