"""Scalar truth-table controls of the reader/collision bridge, not a Lean proof."""
from pathlib import Path
import json
r=Path(__file__).resolve().parent
dfa=json.loads((r/'learned-reader.json').read_bytes())
cells=0;profiles={}
for width in range(2,10):
    P=1<<width;allrows=[]
    for initial in range(1<<width):
        row=[(initial>>j)&1 for j in range(width)];ps=[0]*width
        for t in range(P):
            for j,v in enumerate(row):ps[j]|=v<<t
            # Literal Rule 30 table: physical left is the same marching cell.
            row=[(30>>((row[j]<<2)|((row[j-1] if j else 0)<<1)|(row[j-2] if j>=2 else 0)))&1 for j in range(width)]
            cells+=width
        assert row==[(initial>>j)&1 for j in range(width)]
        allrows.append(ps)
    profiles[width]=allrows
def future(p,P):return (p>>1)|((p&1)<<(P-1))
def state(a,b,n):
    q=0
    for j in range(n):q=dfa['transitions'][q][2*((a>>j)&1)+((b>>j)&1)]
    return q
counts={'accepted_pairs':0,'non16_pairs':0,'state16_pairs':0,'permanent_extension_checks':0}
examples={};needed=None;violations=[]
for width in range(2,9):
    P=1<<width;mask=(1<<P)-1
    for a,ap in enumerate(profiles[width]):
        for b,bp in enumerate(profiles[width]):
            q=state(a,b,width)
            if q not in dfa['accepting']:continue
            counts['accepted_pairs']+=1
            assert ap[-1]==bp[-1]
            examples.setdefault(q,{'initial_a':a,'initial_b':b,'width':width,'state':q})
            if q!=16:
                counts['non16_pairs']+=1
                assert ap[-1]|ap[-2]==bp[-1]|bp[-2]
                for x,y in [(0,1),(1,0)]:
                    az=profiles[width+1][a|(x<<width)][-1]
                    bz=profiles[width+1][b|(y<<width)][-1]
                    assert az^bz==(1<<(1<<(width+1)))-1
                    counts['permanent_extension_checks']+=1
            else:
                counts['state16_pairs']+=1
                assert future(ap[-1],P)==ap[-1]^mask
                d=ap[-2]^bp[-2];assert future(future(d,P),P)==d
                if (ap[-1]|ap[-2])!=(bp[-1]|bp[-2]):
                    violations.append((width,a,b))
                    if needed is None:
                        az=profiles[width+1][a][-1];bz=profiles[width+1][b|(1<<width)][-1]
                        assert az^bz!=(1<<(1<<(width+1)))-1
                        needed={'width':width,'initial_a':a,'initial_b':b,'state':q,
                                'extended_a':a,'extended_b':b|(1<<width),
                                'first_lost_difference':next(t for t in range(1<<(width+1)) if ((az^bz)>>t)&1==0)}
assert counts['state16_pairs']>0 and violations and needed is not None
cases=list(examples.values())+[dict(needed,check_extension=True)]
(r/'control-cases.json').write_text(json.dumps(cases,indent=2)+'\n',encoding='utf-8')
out={'passed':True,'literal_cells_checked':cells,'exhaustive_pair_widths':[2,8],**counts,
     'state16_cannot_be_treated_as_permanent':needed,'negative_control_witnesses':len(violations),
     'Lean_verified':False,'finite_controls_only':True,'sink_separation_proved':False,'full_problem_solved':False}
(r/'independent-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
