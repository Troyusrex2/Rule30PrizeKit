"""Exact sufficient-condition checker on all finite cyclic words.

No Rule30 certificate is supplied here. A positive Python result still needs
an independent Lean soundness proof. Unlike a finite-horizon check, reachability
below tests language inclusion at every word length, not a sampled period.
"""
from collections import deque
import json

def accepts(dfa,word):
    state=dfa['start']
    for a,b in word:state=dfa['delta'][state][2*a+b]
    return state in dfa['accept']

def witness(parent,node,edge=None):
    out=[]
    if edge is not None:out.append(edge)
    while parent[node] is not None:
        node,letter=parent[node];out.append(letter)
    return list(reversed(out))

def validate(dfa,zero_forcing_control=False):
    delta=dfa['delta'];m=len(delta);start=dfa['start'];F=set(dfa['accept'])
    assert m and 0<=start<m and F<=set(range(m))
    assert all(len(row)==4 and all(0<=s<m for s in row) for row in delta)
    result={'states':m,'scope':'exact finite-word DFA sufficient criterion, not a Lean certificate','root':None,'closure':None,'separation':None}
    # Every nonempty all-zero pair word is accepted.
    seen=set();state=start;n=0
    while state not in seen:
        seen.add(state);state=delta[state][0];n+=1
        if state not in F:result['root']={'length':n};break
    # Cyclic running-XOR transduction: accepted(a,b) -> accepted(b,c).
    for initial in (0,1):
        initialnode=(start,start,initial,False);parent={initialnode:None};queue=deque([initialnode])
        while queue and result['closure'] is None:
            node=queue.popleft();si,so,c,used=node
            if used and c==initial and si in F and so not in F:
                result['closure']={'letters':witness(parent,node),'initial_c':initial};break
            for a in (0,1):
                for b in (0,1):
                    nextc=c if zero_forcing_control else c^(a|b)
                    nxt=(delta[si][2*a+b],delta[so][2*b+c],nextc,True)
                    if nxt not in parent:parent[nxt]=(node,(a,b,c));queue.append(nxt)
        if result['closure'] is not None:break
    # An accepted OR-cover pair must have second coordinate of cyclic period2.
    # Prefix record=(lengthclass,first0,first1,last2,last1,local_violation).
    root=(start,(0,0,0,0,0,False));parent={root:None};queue=deque([root])
    while queue:
        node=queue.popleft();state,rec=node;length,f0,f1,p0,p1,bad=rec
        if length==2 and state in F and (bad or p0!=f0 or p1!=f1):
            result['separation']={'letters':witness(parent,node)};break
        for a,b in [(0,1),(1,0),(1,1)]:
            if length==0:new=(1,b,0,0,b,False)
            elif length==1:new=(2,f0,b,f0,b,False)
            else:new=(2,f0,f1,p1,b,bad or b!=p0)
            nxt=(delta[state][2*a+b],new)
            if nxt not in parent:parent[nxt]=(node,(a,b));queue.append(nxt)
    # Replay every extracted counterexample independently of reachability states.
    if result['root'] is not None:assert not accepts(dfa,[(0,0)]*result['root']['length'])
    if result['closure'] is not None:
        triples=result['closure']['letters'];q=len(triples);assert q
        assert accepts(dfa,[(a,b) for a,b,c in triples])
        assert not accepts(dfa,[(b,c) for a,b,c in triples])
        for t,(a,b,c) in enumerate(triples):
            expected=c if zero_forcing_control else ((30>>(4*c+2*a+b))&1)
            assert triples[(t+1)%q][2]==expected
    if result['separation'] is not None:
        pairs=result['separation']['letters'];q=len(pairs);assert q
        assert accepts(dfa,pairs) and all(a or b for a,b in pairs)
        assert any(pairs[t][1]!=pairs[(t+2)%q][1] for t in range(q))
    result['passed']=all(result[k] is None for k in ['root','closure','separation'])
    return result

def period_two_dfa():
    # Exact recognizer of words whose second-coordinate circular word has period2.
    initial=(0,0,0,0,0,False);states=[initial];index={initial:0};delta=[]
    for rec in states:
        length,f0,f1,p0,p1,bad=rec;row=[]
        for a,b in [(0,0),(0,1),(1,0),(1,1)]:
            if length==0:new=(1,b,0,0,b,False)
            elif length==1:new=(2,f0,b,f0,b,False)
            else:new=(2,f0,f1,p1,b,bad or b!=p0)
            if new not in index:index[new]=len(states);states.append(new)
            row.append(index[new])
        delta.append(row)
    F=[i for i,(length,f0,f1,p0,p1,bad) in enumerate(states) if length<2 or not(bad or p0!=f0 or p1!=f1)]
    return {'start':0,'delta':delta,'accept':F}

if __name__=='__main__':
    from pathlib import Path
    import itertools,time
    tick=time.monotonic();dfa=period_two_dfa();controls=0
    for n in range(1,9):
        for bits in itertools.product((0,1),repeat=n):
            expected=all(bits[t]==bits[(t+2)%n] for t in range(n))
            assert accepts(dfa,[(0,b) for b in bits])==expected;controls+=1
    yes=validate(dfa,True);assert yes['passed']
    no=validate(dfa);assert no['root'] is None and no['separation'] is None and no['closure'] is not None
    universal=validate({'start':0,'delta':[[0]*4],'accept':[0]});assert universal['root'] is None and universal['closure'] is None and universal['separation'] is not None
    rootonly=validate({'start':0,'delta':[[0,1,1,1],[1,1,1,1]],'accept':[0]});assert rootonly['root'] is None and rootonly['closure'] is not None and rootonly['separation'] is None
    out={'scope':'validator controls only; no Rule30 invariant found','scalar_recognizer_controls':controls,'positive_zero_forcing_control':yes,'negative_rule30_control':no,'universal_acceptor_control':universal,'root_only_control':rootonly,'seconds':time.monotonic()-tick}
    (Path(__file__).resolve().parent/'DFA-VALIDATOR-CONTROLS.json').write_bytes((json.dumps(out,indent=2)+'\n').encode())
    print(json.dumps({'controls_passed':True,'recognizer_controls':controls,'positive_dfa_states':len(dfa['delta']),'seconds':out['seconds'],'rule30_certificate_found':False}))
