"""Literal Rule 30 causal cones, independent of profile integration and Lean."""
from pathlib import Path
import json
root=Path(__file__).resolve().parent
data=json.loads((root/'explicit-tail.json').read_bytes());M=data['prefix_length'];tail=data['shared_tail']
def p(which,k):return data[which+'_prefix'][k] if k<M else tail[(k-M)%len(tail)]
def bit(which,t,k):return (p(which,k)>>(t%8))&1
def literal(row):return [(30>>((row[k]<<2)|(row[k+1]<<1)|row[k+2]))&1 for k in range(len(row)-2)]
steps=128;interior=32;checks=0
for which in ['a','b']:
    row=[bit(which,0,k) for k in range(2*steps+interior)]
    for t in range(steps+1):
        assert all(v==bit(which,t,k) for k,v in enumerate(row))
        checks+=len(row)
        if t<steps:row=literal(row)
for t in range(steps+1):
    assert bit('a',t,0)==bit('b',t,0)
    assert bit('a',t,4)!=bit('b',t,4)
    assert all(bit('a',t,k)==bit('b',t,k) for k in range(5,32))
assert bit('a',0,5)!=bit('a',1,5)
assert [k for k in range(32) if bit('a',0,k)!=bit('b',0,k)]==[1,2,3,4]
old=[85,87,168,212,172,178,202,43]
def oldp(k):return old[k if k<4 else 4+(k-4)%4]
for k in range(1,33):
    for t in range(8):assert bit('a',t,k)==((oldp(k)>>((t+6)%8))&1)
for t in range(8):assert bit('a',t,0)!=((oldp(0)>>((t+6)%8))&1)
bad=tail.copy();bad[0]^=1
def badbit(t,k):
    v=data['a_prefix'][k] if k<M else bad[(k-M)%len(bad)]
    return (v>>(t%8))&1
assert any(badbit(t+1,k)!=((30>>((badbit(t,k)<<2)|(badbit(t,k+1)<<1)|badbit(t,k+2)))&1)
           for t in range(8) for k in range(M+len(tail)))
def right_bounded_trace(word,n):
    row=[(word>>j)&1 for j in range(n)];initial=row.copy();profile=0;P=1<<(n-1)
    for t in range(P):
        profile|=row[-1]<<t
        row=[row[j]^((row[j-1] if j>0 else 0)|(row[j-2] if j>1 else 0)) for j in range(n)]
    assert row==initial
    return profile,P
a,P=right_bounded_trace(1,5);b,_=right_bounded_trace(23,5);d=a^b
assert d==0x1111 and not (d&((d>>1)|((d&1)<<(P-1))))
assert d!=((d>>2)|((d&3)<<(P-2)))
out={'passed':True,'literal_causal_cells_checked':checks,'time_steps':steps,
     'head_equal_and_source_opposite_checked_through':steps,'initial_difference_depths':[1,2,3,4],
     'common_tail_shared_from_depth':5,'known_loss_precursor_matched_after_time_shift':6,
     'precursor_head_complemented':True,'corrupt_tail_rejected':True,
     'golden_difference_dichotomy_falsified':{'width':5,'a_initial':1,'b_initial':23,'delta_hex':hex(d)},
     'Lean_verified':False,'reader_completeness_proved':False,'full_problem_solved':False}
(root/'independent-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
