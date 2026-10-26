"""Reduce a cubic-moment witness using its exact cyclic time translates."""
from pathlib import Path
import json,time,itertools,numpy as np
r=Path(__file__).resolve().parent;START=time.monotonic()
old=json.loads((r/'cubic-negative-witness.json').read_bytes());P=old['clock'];ws=old['witness'];S=len(ws)
N=max(x['parent_width'] for x in ws);state=np.zeros((S,N),dtype=np.uint8)
rs=np.array([int(x['OR_profile_hex'],16) for x in ws],dtype=np.uint64)
gs=np.array([int(x['newer_profile_hex'],16) for x in ws],dtype=np.uint64)
hs=np.array([int(x['older_profile_hex'],16) for x in ws],dtype=np.uint64)
for j,x in enumerate(ws):
    z=int(x['parent_initial_hex'],16)<<(N-x['parent_width'])
    for k in range(N):state[j,k]=(z>>k)&1
initial=state.copy();byprofile={};records=[];translated=[];labels=[]
lookup=np.array([(30>>i)&1 for i in range(8)],dtype=np.uint8)
left=np.zeros_like(state);right=np.zeros_like(state)
def rotate(xs,d):return xs.copy() if d==0 else (xs>>d)|(xs<<(P-d))
for d in range(P):
    rotated=rotate(rs,d);rg=rotate(gs,d);rh=rotate(hs,d)
    assert np.array_equal(state[:,-1],rg&1) and np.array_equal(state[:,-2],rh&1)
    packed=np.packbits(state,axis=1,bitorder='little');ids=[]
    for j,key in enumerate(rotated):
        key=int(key);z=int.from_bytes(packed[j].tobytes(),'little')
        if key in byprofile:
            i=byprofile[key];assert records[i]['initial']==z and records[i]['g']==int(rg[j]) and records[i]['h']==int(rh[j])
        else:
            i=len(records);byprofile[key]=i;records.append({'initial':z,'g':int(rg[j]),'h':int(rh[j]),'r':key})
        ids.append(i)
    assert len(set(ids))==S
    translated.append(ids);labels.append(int(state[:,-1].sum())%2)
    left[:,1:]=state[:,:-1];right[:,2:]=state[:,:-2]
    state=lookup[(state<<2)|(left<<1)|right]
assert np.array_equal(state,initial)
M=len(records);shifts=[]
for ids in translated:
    b=np.zeros(M,dtype=np.uint8);b[ids]=1
    shifts.append(int.from_bytes(np.packbits(b,bitorder='little').tobytes(),'little'))
jets=shifts[:];jl=labels[:];coeff=[1<<k for k in range(P)]
for bit in [1<<k for k in range(P.bit_length()-1)]:
    for k in range(P):
        if k&bit:jets[k]^=jets[k^bit];jl[k]^=jl[k^bit];coeff[k]^=coeff[k^bit]
positive=[i for i in range(P) if jl[i]];assert positive
start=min(positive,key=lambda i:jets[i].bit_count());best=jets[start];comb=coeff[start]
zero=[(jets[i],coeff[i]) for i in range(P) if not jl[i] and jets[i]]
zero += [(jets[i]^jets[j],coeff[i]^coeff[j]) for i,j in itertools.combinations(positive,2) if jets[i]!=jets[j]]
moves=0
while moves<100:
    weight=best.bit_count();pick=None
    for v,c in zero:
        w=(best^v).bit_count()
        if w<weight:weight=w;pick=(v,c)
    if pick is None:break
    best^=pick[0];comb^=pick[1];moves+=1
chosen=[rec for i,rec in enumerate(records) if (best>>i)&1]
assert len(chosen)%2==0 and sum(x['initial']>>(N-1)&1 for x in chosen)%2==1
obs=[sum((x['r']>>t&1)<<j for j,x in enumerate(chosen)) for t in range(P)]
allones=(1<<len(chosen))-1;checks=1
for degree in range(1,4):
    for ix in itertools.combinations(range(P),degree):
        v=allones
        for t in ix:v&=obs[t]
        assert v.bit_count()%2==0
        checks+=1
witness=[]
for x in chosen:
    z=x['initial'];leading=(z&-z).bit_length()-1 if z else N
    witness.append({'parent_width':N-leading,'parent_initial_hex':hex(z>>leading),
                    'older_profile_hex':hex(x['h']),'newer_profile_hex':hex(x['g']),'OR_profile_hex':hex(x['r'])})
new={'clock':P,'witness_size':len(witness),'witness':witness,
     'maximum_parent_width':max(x['parent_width'] for x in witness),
     'monomials_independently_checked':checks,'target_xor':1,
     'source':'time-translate compression of original witness','translation_coefficients_hex':hex(comb)}
(r/'cubic-negative-witness-sparse.json').write_text(json.dumps(new,indent=2)+'\n',encoding='utf-8')
out={'passed':True,'original_size':S,'translation_union_rows':M,'compressed_size':len(witness),
     'greedy_moves':moves,'direct_OR_moments_checked':checks,'mode_aggregate_bits':labels,
     'seconds':round(time.monotonic()-START,3),'Lean_verified':False,'full_problem_solved':False}
(r/'cubic-sparsify.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
