"""Independent packed-row and finite affine controls; not a kernel proof."""
from pathlib import Path
import itertools,json
r=Path(__file__).resolve().parent
def pack(x,y,z):return x+2*y+4*z
def act(p,s):
    a,b,c,d,e,f=p;x,y,z=(s>>0)&1,(s>>1)&1,(s>>2)&1
    return pack(x^a,y^b^(c&x),z^d^(e&x)^(f&y))
def gate(A,u,s):
    x,y,z=(s>>0)&1,(s>>1)&1,(s>>2)&1
    return pack(x^A,y^(x|u),z^(y|x))
def fit(F):
    z,x,y=F(0),F(1),F(2)
    return (z&1,(z>>1)&1,((x^z)>>1)&1,(z>>2)&1,((x^z)>>2)&1,((y^z)>>2)&1)
def compose(p,q):
    a,b,c,d,e,f=p;A,B,C,D,E,F=q
    return (A^a,B^b^(c&A),C^c,D^d^(e&A)^(f&B),E^e^(f&C),F^f)
ps=list(itertools.product([0,1],repeat=6));compositions=0;quartics=0;pairs=0
for p in ps:
    for s in range(8):
        t=s
        for _ in range(4):t=act(p,t)
        assert t==s;quartics+=1
    for q in ps:
        pq=compose(p,q)
        for s in range(8):assert act(pq,s)==act(p,act(q,s));compositions+=1
for A,u,B,v in itertools.product([0,1],repeat=4):
    F=lambda s:gate(B,v,gate(A,u,s));p=fit(F)
    for s in range(8):assert act(p,s)==F(s);pairs+=1
bad=0
for _ in range(4):bad=gate(1,0,bad)
assert bad!=0
two_step_cells=0
for bits in itertools.product([0,1],repeat=5):
    row=list(bits)
    for _ in range(2):row=[(30>>((row[j+2]<<2)|(row[j+1]<<1)|row[j]))&1 for j in range(len(row)-2)]
    v,w,x,y,z=bits
    assert row[0]==(z^((w|v)&(1^x^y)));two_step_cells+=1
period_controls=[];row_updates=0;scalar=0
for width in range(1,14):
    P=1<<((2*width-1)//3);mask=(1<<width)-1
    for initial in range(1<<width):
        row=initial
        for _ in range(P):
            if width<=6:
                literal=sum(((30>>((((row>>j)&1)<<2)|((((row>>(j-1))&1) if j else 0)<<1)|(((row>>(j-2))&1) if j>=2 else 0)))&1)<<j for j in range(width))
                assert literal==((row^((row<<1)|(row<<2)))&mask);scalar+=width
            row=(row^((row<<1)|(row<<2)))&mask;row_updates+=1
        assert row==initial,(width,initial,P)
    period_controls.append({'width':width,'clock':P,'all_initial_rows':1<<width,'passed':True})
out={'passed':True,'affine_composition_cases':compositions,'quartic_cases':quartics,
     'two_gate_cases':pairs,'literal_two_step_patterns':two_step_cells,'odd_period_negative_control_return_after_four':bad,
     'period_controls':period_controls,'packed_row_updates':row_updates,
     'literal_truth_table_cells':scalar,'Lean_verified':False,'full_problem_solved':False}
(r/'independent-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
