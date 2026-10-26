from pathlib import Path
import json
r=Path(__file__).resolve().parent
e=json.loads((r/'nonalternating-resync.json').read_bytes())['reports'][-1]['example']
P=8;mask=255
def integral(g,bit):
    x=g;s=1
    while s<P:x^=x<<s;s*=2
    return ((x<<1)&mask)^(mask if bit else 0)
u,v=e['seed_common'];assert [u,v]==[43,202]
a=integral(u|v,0);b=a^mask;pa=pb=v;aa=[a];bb=[b]
for abit,bbit in e['extension_initials']:
    na=integral(pa|a,abit);nb=integral(pb|b,bbit)
    pa,a=a,na;pb,b=b,nb;aa.append(a);bb.append(b)
A=list(reversed(aa));B=list(reversed(bb));tail=[202,43,172,178];M=len(A)
def at(prefix,k):return prefix[k] if k<M else tail[(k-M)%4]
for prefix in (A,B):
    for k in range(M+4):
        x=at(prefix,k);dx=x^((x>>1)|((x&1)<<7))
        assert dx==(at(prefix,k+1)|at(prefix,k+2))
assert [k for k in range(M+4) if (at(A,k)^at(B,k))&1]==[7]
assert A[0]==B[0] and (A[7]^B[7])==255
assert A[0]!=((A[0]>>2)|((A[0]&3)<<6))
ORa=A[1]|A[2];ORb=B[1]|B[2];assert ORa==ORb and ORa not in (0,255)
result={'temporal_clock':8,'a_prefix':A,'b_prefix':B,'shared_tail':tail,'prefix_length':M,
        'initial_difference_support':[7],'source_depth':7,'head_profile':A[0],
        'nonconstant_common_OR_profile':ORa,'not_a_finite_background_counterexample':True,
        'Lean_verified':False,'reader_completeness_proved':False,'full_problem_solved':False}
(r/'single-flip-tail.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
