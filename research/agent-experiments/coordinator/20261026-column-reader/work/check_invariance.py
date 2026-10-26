"""Finite product checks necessary unbounded invariance of the candidate DFA.
This does not prove completeness of the candidate equality language.
"""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
dfa=json.loads((ROOT/'learned-reader.json').read_bytes())['dfa']
def out(s,p,q):
    a=(s>>1)^((p>>1)|(q>>1));b=(s&1)^((p&1)|(q&1))
    return (a<<1)|b
initial=(dfa['start'],dfa['start'],0,0)
states=[initial];parents=[None];index={initial:0};at=0;bad=None;edges=[]
while at<len(states):
    a,b,p,q=states[at]
    if (a in dfa['accepting']) != (b in dfa['accepting']):bad=('invariance',at);break
    if a in dfa['accepting'] and p not in [0,3]:bad=('last_bit_soundness',at);break
    row=[]
    for sym in range(4):
        result=(dfa['transitions'][a][sym],dfa['transitions'][b][out(sym,p,q)],sym,p)
        if result not in index:index[result]=len(states);states.append(result);parents.append((at,sym))
        row.append(index[result])
    edges.append(row);at+=1
word=None
if bad:
    word=[];i=bad[1]
    while parents[i] is not None:i,s=parents[i];word.append(s)
    word.reverse()
result={'closed':bad is None,'states':states,'edges':edges,'counterexample_kind':bad[0] if bad else None,
        'counterexample':word,'Lean_verified':False,'completeness_proved':False}
(ROOT/'invariance-product.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'closed':result['closed'],'states':len(states),'counterexample':word}))
