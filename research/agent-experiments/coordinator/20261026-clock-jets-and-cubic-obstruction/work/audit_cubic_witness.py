"""Independent literal initial-word and all cubic head-moment validation."""
from pathlib import Path
import json,itertools,time,sys,numpy as np
r=Path(__file__).resolve().parent;START=time.monotonic()
source=sys.argv[1] if len(sys.argv)>1 else 'cubic-negative-witness.json'
output=sys.argv[2] if len(sys.argv)>2 else 'cubic-witness-audit.json'
j=json.loads((r/source).read_bytes());P=j['clock'];ws=j['witness'];S=len(ws)
N=max(x['parent_width'] for x in ws);width=N+1
print(json.dumps({'witness_rows':S,'uniform_word_width':width,'full_cycle':2*P}),flush=True)
initial=np.zeros((S,width),dtype=np.uint8);numbers=[]
def canonical(z,n):
    if not z:return True
    i=(z&-z).bit_length()-1
    return i>=n-2 or (i+3<n and ((z>>(i+1))&1)==((z>>(i+2))&1))
for row,x in enumerate(ws):
    m=x['parent_width'];v=int(x['parent_initial_hex'],16);assert 0<=v<1<<m
    z=v<<(N-m);assert canonical(z,width)
    numbers.append(z)
    for k in range(width):initial[row,k]=(z>>k)&1
assert len(set(numbers))==S and S%2==0
target_xor=int(initial[:,-2].sum())%2;assert target_xor==1
older=np.array([int(x['older_profile_hex'],16) for x in ws],dtype=np.uint64)
newer=np.array([int(x['newer_profile_hex'],16) for x in ws],dtype=np.uint64)
orprofiles=np.array([int(x['OR_profile_hex'],16) for x in ws],dtype=np.uint64)
assert np.array_equal(older|newer,orprofiles)
lookup=np.array([(30>>i)&1 for i in range(8)],dtype=np.uint8)
state=initial.copy();left=np.zeros_like(state);right=np.zeros_like(state);heads=[]
for t in range(2*P):
    if t==P:assert np.array_equal(state[:,:-1],initial[:,:-1])
    assert np.array_equal(state[:,-2],(newer>>(t%P))&1)
    assert np.array_equal(state[:,-3],(older>>(t%P))&1)
    heads.append(int.from_bytes(np.packbits(state[:,-1],bitorder='little').tobytes(),'little'))
    left[:,1:]=state[:,:-1];right[:,2:]=state[:,:-2]
    state=lookup[(state<<2)|(left<<1)|right]
assert np.array_equal(state,initial)
# Literal head functions, not the source's OR functions, are checked here.
monomials=1;allones=(1<<S)-1
for degree in range(1,4):
    for ix in itertools.combinations(range(2*P),degree):
        v=allones
        for t in ix:v&=heads[t]
        assert v.bit_count()%2==0,(degree,ix)
        monomials+=1
out={'passed':True,'witness_rows':S,'canonical_word_width':width,'full_cycle':2*P,
     'all_initial_words_canonical':True,'all_initial_words_distinct':True,
     'literal_rule30_cells':S*width*2*P,'all_rows_return_after_full_cycle':True,
     'parent_profiles_match_source':True,'head_monomials_independently_checked':monomials,
     'penultimate_initial_bits_xor':target_xor,'all_constant_to_cubic_head_moments_zero':True,
     'no_uniform_cubic_decoder_certificate':True,'Lean_verified':False,
     'canonical_observer_refuted':False,'full_problem_solved':False,
     'seconds':round(time.monotonic()-START,3)}
(r/output).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
