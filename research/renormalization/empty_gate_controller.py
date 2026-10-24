"""Untrusted finite controllers extracted from the empty-right prefix automaton."""
from collections import deque

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components

from right_prefix_safety import double_step


def make_controller(length=7,width=16):
    mask=(1<<width)-1;a=1
    for _ in range(146):a=double_step(a)
    states=[a&mask];index={states[0]:0};edges=[]
    for q in states:
        row=[]
        for tail in range(4):
            nxt=double_step(q|(tail<<width))&mask
            if nxt not in index:index[nxt]=len(states);states.append(nxt)
            row.append(index[nxt])
        edges.append(row)
    rr=np.repeat(np.arange(len(states)),4);cc=np.array(edges).reshape(-1)
    count,lab=connected_components(csr_matrix((np.ones(len(cc)),(rr,cc)),shape=(len(states),len(states))),
                                   directed=True,connection='strong')
    core=max(range(count),key=lambda c:int(np.sum(lab==c)))
    members=np.flatnonzero(lab==core).tolist()
    assert all(lab[n]==core for q in members for n in edges[q])
    local={q:i for i,q in enumerate(members)}
    values=[states[q] for q in members]
    successors=[sorted(set(local[n] for n in edges[q])) for q in members]
    a=1;entry=None
    for t in range(1025):
        if (a&mask) in index and lab[index[a&mask]]==core:entry=t;break
        a=double_step(a)
    assert entry is not None
    words=[{q&1} for q in values];previous=None
    for size in range(2,length+2):
        previous=words
        words=[{(values[q]&1)|(suffix<<1) for nxt in successors[q] for suffix in previous[nxt]}
               for q in range(len(values))]
    oldwords=set().union(*previous);transitions=set().union(*words)
    controller={'untrusted_computation':True,'Lean_verified':False,'width':width,'entry_cycle':entry,
                'core_states':values,'successors':successors,'length':length,
                'words':sorted(oldwords),'transition_words':sorted(transitions)}
    if length+1<=8:
        for q,w in zip(values,words):
            actual=0;v=q
            for j in range(length+1):actual|=(v&1)<<j;v=double_step(v)
            assert w=={actual}
        controller['direct_cone_word_control_passed']=True
    return controller
