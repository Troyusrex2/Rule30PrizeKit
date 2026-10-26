"""Exact product reachability at a fixed temporal clock; width is unbounded.
The finite graph is a diagnostic until a kernel proof checks its closure.
"""
from pathlib import Path
from collections import deque
import hashlib,json,time
ROOT=Path(__file__).resolve().parent
dfa=json.loads((ROOT/'learned-reader.json').read_bytes())['dfa']
start=time.monotonic();reports=[];CAP=250000

def integral(g,initial,P):
    mask=(1<<P)-1;x=g;s=1
    while s<P:x^=x<<s;s*=2
    return ((x<<1)&mask)^(mask if initial else 0)

for P in [2,4,8,16]:
    initial=(0,0,0,0,dfa['start']);states=[initial];parents=[None];index={initial:0};at=0
    closed=True;bad=None;edges=0;begin=time.monotonic()
    while at<len(states):
        if len(states)>CAP:closed=False;break
        if time.monotonic()-start>60:closed=False;break
        a0,a1,b0,b1,q=states[at]
        if (a1==b1)!=(q in dfa['accepting']):bad=at;closed=False;break
        ga,gb=a0|a1,b0|b1
        if ga.bit_count()%2==0 and gb.bit_count()%2==0:
            for sym in range(4):
                a2=integral(ga,sym>>1,P);b2=integral(gb,sym&1,P)
                state=(a1,a2,b1,b2,dfa['transitions'][q][sym]);edges+=1
                if state not in index:
                    index[state]=len(states);states.append(state);parents.append((at,sym))
        at+=1
    counterexample=None
    if bad is not None:
        word=[];j=bad
        while parents[j] is not None:j,s=parents[j];word.append(s)
        counterexample=list(reversed(word))
    result={'temporal_clock':P,'states':len(states),'processed':at,'edges':edges,
            'closed':closed,'counterexample':counterexample,'seconds':round(time.monotonic()-begin,3),
            'unbounded_spatial_width_in_this_closed_graph':closed,'Lean_verified':False}
    if closed:
        payload=json.dumps({'states':states,'parents':parents},separators=(',',':')).encode()
        name=f'clock-product-{P}-graph.json';(ROOT/name).write_bytes(payload)
        result['graph_file']=name;result['graph_sha256']=hashlib.sha256(payload).hexdigest()
    reports.append(result);print(json.dumps(result),flush=True)
    if bad is not None:break
out={'reports':reports,'all_temporal_clocks_proved':False,'Lean_verified':False,'full_problem_solved':False}
(ROOT/'clock-product.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
