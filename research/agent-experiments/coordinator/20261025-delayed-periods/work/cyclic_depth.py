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

# Exhaustive independent small-ring check of the transfer construction.
controls=0
for p in range(1,9):
    for a in itertools.product(range(2),repeat=p):
        w=rule_word(a);found=preimages(w)
        assert canonical(bytes(a)) in found
        assert canonical(bytes(a))==min(bytes(a[i:]+a[:i]) for i in range(p))[:len(primitive(bytes(a)))]
        controls+=1

# Complete temporal tails for both possible alternating free phases.
bases=set()
for first in (0,1):
    cycle=core.spatial_cycle([],first);entry=cycle['entry_depth'];p=cycle['period']
    prev=0;cur=sum((1 if t%2==0 else first^(t//2%2))<<t for t in range(4));columns={}
    for d in range(1,entry+p):
        columns[d]=cur
        shifted=(cur>>1)|((cur&1)<<3)
        prev,cur=cur,(shifted^(cur|prev))&15
    for t in range(4):bases.add(canonical(bytes(columns[d]>>t&1 for d in range(entry,entry+p))))

seen={w:0 for w in bases};frontier=set(bases);records=[];best=None;stop=None
with (root/'cyclic-depth.partial.jsonl').open('w',encoding='utf-8') as log:
    for depth in range(4097):
        if not frontier:stop='exact_finite_closed_preimage_set';break
        new=set()
        for w in sorted(frontier,key=lambda a:(len(a),a)):
            if time.monotonic()-start>230:stop='internal_time_budget';break
            for v,meta in preimages(w).items():
                if len(v)>16384:stop='period_cap';break
                if v in seen:continue
                seen[v]=depth+1;new.add(v)
                rec={'depth':depth+1,'word':''.join(map(str,v)),'period':len(v),
                     'black':sum(v),'density':str(Fraction(sum(v),len(v))),
                     'parent_sha256':hashlib.sha256(w).hexdigest(),'sha256':hashlib.sha256(v).hexdigest(),
                     'lift':meta}
                records.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
                if best is None or Fraction(rec['density'])<Fraction(best['density']):
                    best=rec;print(json.dumps({'new_generic_minimum':{k:rec[k] for k in ['depth','period','black','density','sha256']}}),flush=True)
            if stop:break
            if len(seen)>50000:stop='node_cap';break
        print(json.dumps({'depth':depth+1,'new_nodes':len(new),'total':len(seen),
                          'max_period':max(map(len,seen)),'elapsed_seconds':time.monotonic()-start}),flush=True)
        if stop:break
        frontier=new
    else:stop='depth_cap'
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'exhaustive_small_ring_controls':controls,'bases':[''.join(map(str,w)) for w in sorted(bases)],
     'records':records,'nodes':len(seen),'maximum_period':max(map(len,seen)),
     'minimum':best,'stop':stop,'elapsed_seconds':time.monotonic()-start,
     'scope':'Exact periodic preimage graph of temporal tail row words, up to rotations. Superset of actual coupled free traces. Low density does not establish a C3 counterexample for finite R.'}
(root/'cyclic-depth.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['nodes','maximum_period','stop','elapsed_seconds']}))
