"""Search a smaller whole-orbit cubic-moment certificate at clock 64.
The final selected data are checked directly; minimization is only a heuristic.
"""
from pathlib import Path
import json,itertools,time,numpy as np
r=Path(__file__).resolve().parent;START=time.monotonic();P=64;MASK=(1<<P)-1
C=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]];D={0,1,4,5}
def integral(x,b):
    y=x;s=1
    while s<P:y^=y<<s;s*=2
    return ((y<<1)&MASK)^(MASK if b else 0)
states=[(0,0,0)];index={states[0]:0};parents=[None];chosen={}
for at,(u,v,d) in enumerate(states):
    drive=u|v
    if d in D:
        if drive not in chosen:chosen[drive]=at
        else:assert states[chosen[drive]][1]==v
    if drive.bit_count()%2==0:
        for b in range(2):
            nxt=(v,integral(drive,b),C[d][b])
            if nxt not in index:index[nxt]=len(states);states.append(nxt);parents.append((at,b))
def word(i):
    out=[]
    while parents[i] is not None:i,b=parents[i];out.append(b)
    return out[::-1]
def rot(x,d):
    d%=P
    return x if not d else ((x>>d)|(x<<(P-d)))&MASK
orbits=[];seen=set()
for rr,i in chosen.items():
    if rr in seen:continue
    h,g,_=states[i];cycle=[];v=rr
    while v not in seen:
        assert v in chosen and states[chosen[v]][1]==rot(g,len(cycle))
        seen.add(v);cycle.append(v);v=rot(v,1)
    assert v==rr
    xs=word(i);initial=sum(b<<j for j,b in enumerate(xs))
    orbits.append({'period':len(cycle),'r':rr,'g':g,'h':h,'width':len(xs),'initial':initial,'cycle':cycle})
assert len(seen)==len(chosen)
K=len(orbits);rr=np.array([o['r'] for o in orbits],dtype=np.uint64)
gg=np.array([o['g'] for o in orbits],dtype=np.uint64)
masks=np.array([(1<<o['period'])-1 for o in orbits],dtype=np.uint64)
rots=np.array([rr if d==0 else (rr>>d)|(rr<<(P-d)) for d in range(P)])
def parities(a):
    a=a.copy()
    for shift in [32,16,8,4,2,1]:a^=a>>shift
    return a&1
def pack(a):return int.from_bytes(np.packbits(a.astype(np.uint8),bitorder='little').tobytes(),'little')
features=[pack(np.array([o['period']%2 for o in orbits])),pack(parities(rr&masks))]
for b in range(1,P):features.append(pack(parities(rr&rots[b]&masks)))
for b,c in itertools.combinations(range(1,P),2):features.append(pack(parities(rr&rots[b]&rots[c]&masks)))
target=pack(parities(gg&masks));basis={}
for v in features:
    while v:
        p=v.bit_length()-1
        if p not in basis:basis[p]=v;break
        v^=basis[p]
remaining=target
while remaining and remaining.bit_length()-1 in basis:remaining^=basis[remaining.bit_length()-1]
assert remaining
ordered=sorted(basis.items());positive=[];zero=[]
for j in range(K):
    if j in basis:continue
    d=1<<j
    for p,b in ordered:
        if (b&d).bit_count()%2:d^=1<<p
    assert all((b&d).bit_count()%2==0 for b in basis.values())
    (positive if (target&d).bit_count()%2 else zero).append(d)
assert positive
periodmasks={L:sum(1<<j for j,o in enumerate(orbits) if o['period']==L) for L in [1,2,4,8,16,32,64]}
def cost(v):return sum(L*(v&m).bit_count() for L,m in periodmasks.items())
old=json.loads((r/'cubic-negative-witness.json').read_bytes())
oldset={int(x['OR_profile_hex'],16) for x in old['witness']};oldv=0
for j,o in enumerate(orbits):
    hits=sum(x in oldset for x in o['cycle']);assert hits in [0,o['period']]
    if hits:oldv|=1<<j
assert (oldv&target).bit_count()%2==1 and cost(oldv)==old['witness_size']
positive.sort(key=cost);top=positive[:64]
zero=list(set(zero+[a^b for a,b in itertools.combinations(top,2)]))
starts=[oldv,*positive[:12]];best=oldv;moves=0
for initial in starts:
    cur=initial
    while time.monotonic()-START<75:
        weight=cost(cur);pick=None
        for v in zero:
            w=cost(cur^v)
            if w<weight:weight=w;pick=v
        if pick is None:break
        cur^=pick;moves+=1
    if cost(cur)<cost(best):best=cur
    if time.monotonic()-START>=75:break
assert all((f&best).bit_count()%2==0 for f in features) and (target&best).bit_count()%2==1
selected=[o for j,o in enumerate(orbits) if (best>>j)&1]
witness=[];records=[]
def canonical(z,n):
    if not z:return True
    i=(z&-z).bit_length()-1
    return i>=n-2 or (i+3<n and ((z>>(i+1))&1)==((z>>(i+2))&1))
for o in selected:
    m=o['width'];initial=o['initial'];x=initial
    assert canonical(x,m+1)
    for t in range(o['period']):
        g=(x>>(m-1))&1 if m else 0;h=(x>>(m-2))&1 if m>=2 else 0
        assert g==((o['g']>>t)&1) and (g|h)==((o['r']>>t)&1)
        assert canonical(x,m+1)
        witness.append({'parent_width':m,'parent_initial_hex':hex(x),'older_profile_hex':hex(rot(o['h'],t)),
                        'newer_profile_hex':hex(rot(o['g'],t)),'OR_profile_hex':hex(rot(o['r'],t))})
        x=(x^((x<<1)|(x<<2)))&((1<<m)-1)
    assert x==initial
    records.append({'period':o['period'],'parent_width':m,'parent_initial_hex':hex(initial),
                    'older_profile_hex':hex(o['h']),'newer_profile_hex':hex(o['g']),'OR_profile_hex':hex(o['r'])})
new={'clock':P,'witness_size':len(witness),'witness':witness,'maximum_parent_width':max(x['parent_width'] for x in witness),
     'monomials_independently_checked':len(features),'target_xor':1,'source':'whole-orbit moment-kernel minimization'}
(r/'cubic-negative-witness-orbit-min.json').write_text(json.dumps(new,indent=2)+'\n',encoding='utf-8')
out={'passed':True,'all_OR_orbits':K,'normalized_moments':len(features),'orbit_moment_rank':len(basis),
     'old_orbits':oldv.bit_count(),'old_rows':cost(oldv),'selected_orbits':len(selected),'selected_rows':len(witness),
     'maximum_parent_width':new['maximum_parent_width'],'greedy_moves':moves,'orbit_certificate':records,
     'seconds':round(time.monotonic()-START,3),'Lean_verified':False,'canonical_observer_refuted':False,'full_problem_solved':False}
(r/'orbit-negative-certificate.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='orbit_certificate'}),flush=True)
