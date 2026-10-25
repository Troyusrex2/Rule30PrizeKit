"""All cyclic preimages per periodic word via the proved four-state transfer.

Searches a superset of realizable driver histories. It never labels a low
density cyclic word as an actual finite-right witness or a prize solution.
"""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,time
import feedback_core as core
root=Path(__file__).resolve().parent;start=time.monotonic()
T=((0,3,1,3),(1,2,0,2))

def rule_word(a):
    p=len(a)
    return bytes(a[(i+1)%p]^(a[i]|a[(i-1)%p]) for i in range(p))

def primitive(w):
    # A generic KMP period, independent of a guessed prime factorization.
    pi=[0]*len(w)
    for i in range(1,len(w)):
        j=pi[i-1]
        while j and w[i]!=w[j]:j=pi[j-1]
        if w[i]==w[j]:j+=1
        pi[i]=j
    p=len(w)-pi[-1]
    return w[:p] if len(w)%p==0 else w

def canonical(w):
    w=primitive(w);p=len(w);s=w+w;i=0;j=1;k=0
    while i<p and j<p and k<p:
        if s[i+k]==s[j+k]:k+=1;continue
        if s[i+k]>s[j+k]:
            i=i+k+1
            if i<=j:i=j+1
        else:
            j=j+k+1
            if j<=i:j=i+1
        k=0
    q=min(i,j)
    return s[q:q+p]

def preimages(w):
    p=len(w);monodromy=[]
    for s in range(4):
        for b in w:s=T[b][s]
        monodromy.append(s)
    # White input invokes the kernel-proved F^5=F^3 identity. All-black
    # input has the separate elementary three-cycle and needs three blocks.
    blocks=2 if 0 in w else 3
    out={}
    for initial in range(4):
        s=initial
        for _ in range(3):s=monodromy[s]
        began=s;bits=[]
        for b in w*blocks:
            bits.append(s&1);s=T[b][s]
        assert s==began
        a=bytes(bits)
        assert rule_word(a)==w*blocks
        key=canonical(a)
        out[key]={'state':began,'blocks':blocks,'monodromy':monodromy}
    return out

