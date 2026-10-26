"""Exact regular preimages of unsafe cyclic profiles, with explicit caps.
No automata are widened and a state count alone is never a fixed-point test.
"""
from pathlib import Path
from collections import deque
import json,time
r=Path(__file__).resolve().parent;start=time.monotonic();MAX_STATES=100000
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa']
def diff(a):return ((a>>2)&1)!=(a&1)
def minimize(m):
    T,A,S=m['transitions'],m['accept'],m['starts'];part=[int(a) for a in A];rounds=0
    while True:
        keys={};new=[]
        for i,row in enumerate(T):
            sig=(A[i],*(part[j] for j in row))
            new.append(keys.setdefault(sig,len(keys)))
        rounds+=1
        if new==part:break
        part=new
        if time.monotonic()-start>180:raise RuntimeError('time_cap')
    reps=[None]*len(set(part))
    for i,p in enumerate(part):reps[p]=i
    out={'transitions':[[part[j] for j in T[i]] for i in reps],
         'accept':[A[i] for i in reps],'starts':[part[s] for s in S]}
    return out,rounds
def preimage(m):
    T,A,S=m['transitions'],m['accept'],m['starts'];states=[];index={};rows=[];accept=[]
    def add(x):
        if x not in index:
            if len(states)>=MAX_STATES:raise RuntimeError('composition_state_cap')
            index[x]=len(states);states.append(x)
        return index[x]
    starts=[add((S[q],*(S[reader['transitions'][q][c]] for c in range(4)),0)) for q in range(17)]
    i=0
    while i<len(states):
        s,*rest=states[i];cs=rest[:4];parity=rest[4]
        accept.append(A[s] and (parity!=0 or all(A[c] for c in cs)))
        row=[]
        for a in range(16):
            u,v,up,vp=a>>3,(a>>2)&1,(a>>1)&1,a&1
            outputs=[]
            for c in range(4):
                carry=c^parity;symbol=(v<<3)|((carry>>1)<<2)|(vp<<1)|(carry&1)
                outputs.append(T[cs[c]][symbol])
            nxt=parity^((u|v)<<1)^(up|vp)
            row.append(add((T[s][a],*outputs,nxt)))
        rows.append(row);i+=1
        if time.monotonic()-start>180:raise RuntimeError('time_cap')
    return {'transitions':rows,'accept':accept,'starts':starts},len(states)
def equivalent(a,b):
    pairs=deque((a['transitions'][a['starts'][q]][c],b['transitions'][b['starts'][q]][c],q,(c,))
                for q in range(17) for c in range(16));seen=set()
    while pairs:
        x,y,q,w=pairs.popleft()
        if (x,y) in seen:continue
        seen.add((x,y))
        if a['accept'][x]!=b['accept'][y]:return False,{'q':q,'word':w}
        for c in range(16):pairs.append((a['transitions'][x][c],b['transitions'][y][c],q,w+(c,)))
    return True,{'product_pairs':len(seen)}
def classify(m,q,w):
    s=m['starts'][q]
    for a in w:s=m['transitions'][s][a]
    return m['accept'][s]
def seeds(m):
    s=m['transitions'][m['starts'][0]][0];seen=set();n=1
    while s not in seen:
        seen.add(s)
        if not m['accept'][s]:return False,{'first_white_length':n}
        s=m['transitions'][s][0];n+=1
    return True,{'zero_orbit_states':len(seen)}
controls=[]
for P in [2,4,8,16]:
    for u,v,up,vp,q in json.loads((r/f'clock-product-{P}-graph.json').read_bytes())['states']:
        w=tuple((((u>>t)&1)<<3)|(((v>>t)&1)<<2)|(((up>>t)&1)<<1)|((vp>>t)&1) for t in range(P))
        controls.append((q,w))
m={'transitions':[[1 if diff(a) else 0 for a in range(16)],[1]*16],
   'accept':[False,True],'starts':[0 if q==15 else 1 for q in range(17)]}
history=[];fixed=False;reason=None
try:
    for depth in range(12):
        raw,n=preimage(m);new,rounds=minimize(raw)
        assert all(classify(new,q,w) for q,w in controls)
        seed_ok,seed_data=seeds(new);same,comparison=equivalent(m,new)
        meta={'depth':depth+1,'before_states':len(m['accept']),'composition_states':n,
              'minimal_states':len(new['accept']),'minimization_rounds':rounds,
              'all_seed_lengths_passed':seed_ok,'seed_check':seed_data,'same_language':same,
              'equivalence_domain':'all_nonempty_words',
              'equivalence_or_witness':comparison,'reachable_control_words_checked':len(controls)}
        history.append(meta);print(json.dumps(meta),flush=True)
        (r/f'exact-backward-depth-{depth+1}.json').write_text(json.dumps(new,separators=(',',':'))+'\n',encoding='utf-8')
        if not seed_ok:reason='white_seed_excluded_requires_witness_reconstruction';break
        if same:fixed=True;reason='exact_all_word_fixed_point';break
        m=new
    else:reason='depth_cap'
except RuntimeError as e:reason=str(e)
out={'history':history,'stop_reason':reason,'all_word_fixed_point':fixed,
     'seconds':round(time.monotonic()-start,3),'Lean_verified':False,
     'reader_completeness_proved':False,'full_problem_solved':False}
(r/'exact-backward.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out),flush=True)
