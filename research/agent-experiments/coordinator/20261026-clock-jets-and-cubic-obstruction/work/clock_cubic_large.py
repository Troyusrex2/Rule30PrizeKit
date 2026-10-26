from pathlib import Path
import itertools,json,time,random,platform
import numpy as np
from gf2_block import eliminate,pivot,dual_vector,features
r=Path(__file__).resolve().parent;START=time.monotonic();reports=[]
def pack(bits):
    b=np.packbits(np.array(bits,dtype=np.uint8),bitorder='little');return np.pad(b,(0,(-len(b))%8)).view(np.uint64)
def py_rank(rows):
    basis={}
    for v in rows:
        while v:
            p=v.bit_length()-1
            if p not in basis:basis[p]=v;break
            v^=basis[p]
    return basis
randomizer=random.Random(81961);controls=0
for N in [1,3,8,17,48,73,130]:
  for R in [1,3,9,16,40]:
    raw=[randomizer.getrandbits(N) for _ in range(R)];basis=py_rank(raw)
    for typ in range(2):
      target=randomizer.getrandbits(N) if typ else 0
      if not typ:
        for v in raw:
          if randomizer.randrange(2):target^=v
      residue=target
      while residue and residue.bit_length()-1 in basis:residue^=basis[residue.bit_length()-1]
      matrix=np.array([pack([(v>>j)&1 for j in range(N)]) for v in raw]);t=pack([(target>>j)&1 for j in range(N)])
      rank,piv=eliminate(matrix,t)
      assert rank==len(basis) and (pivot(t)<0)==(residue==0)
      if residue:
        dual=dual_vector(matrix,piv,pivot(t));di=int.from_bytes(dual.tobytes(),'little')
        assert all((v&di).bit_count()%2==0 for v in raw) and (target&di).bit_count()%2==1
      controls+=1
print(json.dumps({'block_controls_passed':controls}),flush=True)
C=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]];D={0,1,4,5}
def integral(x,b,P):
    mask=(1<<P)-1;y=x;s=1
    while s<P:y^=y<<s;s*=2
    return ((y<<1)&mask)^(mask if b else 0)
def graph(P):
    states=[(0,0,0)];index={states[0]:0};parents=[None];chosen={}
    for at,st in enumerate(states):
        u,v,d=st;drive=u|v
        if d in D:
            if drive not in chosen:chosen[drive]=at
            else:assert states[chosen[drive]][1]==v
        if drive.bit_count()%2==0:
            for b in range(2):
                nxt=(v,integral(drive,b,P),C[d][b])
                if nxt not in index:index[nxt]=len(states);states.append(nxt);parents.append((at,b))
        assert len(states)<1500000
    return states,parents,list(chosen.values())
for P in [8,16,32,64]:
    begin=time.monotonic();states,parents,ids=graph(P);M=len(ids);W=(M+63)//64
    outputs=[states[i][0]|states[i][1] for i in ids]
    obs=np.array([pack([(x>>t)&1 for x in outputs]) for t in range(P)])
    target=pack([states[i][1]&1 for i in ids]);original=target.copy()
    mat=features(obs,M);built=time.monotonic()
    print(json.dumps({'clock':P,'profile_states':len(states),'canonical_OR_profiles':M,'matrix_bytes':mat.nbytes,'stage':'eliminating'}),flush=True)
    rank,piv=eliminate(mat,target);res=pivot(target)
    meta={'clock':P,'closed_product_states':len(states),'canonical_OR_profiles':M,
          'cubic_rank':int(rank),'parent_bit_recoverable':res<0,
          'build_seconds':round(built-begin,3),'eliminate_seconds':round(time.monotonic()-built,3)}
    if P<=32:
        small=json.loads((r/'clock-cubic-probe.json').read_bytes())
        old=next(x for x in small['reports'] if x['clock']==P)
        assert rank==old['layers'][-1]['rank'] and (res<0)==old['layers'][-1]['parent_bit_recoverable']
        meta['cross_checked_with_python']=True
    negative=None
    if res>=0:
        dual=dual_vector(mat,piv,res);di=int.from_bytes(dual.tobytes(),'little')
        targetint=int.from_bytes(original.tobytes(),'little');assert (di&targetint).bit_count()%2==1
        obsint=[int.from_bytes(x.tobytes(),'little') for x in obs]
        # Independent scalar check of EVERY monomial, including the constant.
        assert di.bit_count()%2==0;monomials=1
        for degree in range(1,4):
          for ix in itertools.combinations(range(P),degree):
            v=di
            for k in ix:v&=obsint[k]
            assert v.bit_count()%2==0
            monomials+=1
        def word(i):
            out=[]
            while parents[i] is not None:i,b=parents[i];out.append(b)
            return out[::-1]
        witness=[]
        for j,i in enumerate(ids):
            if (di>>j)&1:
                xs=word(i);initial=sum(b<<k for k,b in enumerate(xs))
                witness.append({'parent_width':len(xs),'parent_initial_hex':hex(initial),
                                'older_profile_hex':hex(states[i][0]),'newer_profile_hex':hex(states[i][1]),
                                'OR_profile_hex':hex(outputs[j])})
        negative={'clock':P,'witness_size':len(witness),'witness':witness,
                  'maximum_parent_width':max(x['parent_width'] for x in witness),
                  'monomials_independently_checked':monomials,'target_xor':1}
        (r/'cubic-negative-witness.json').write_text(json.dumps(negative,indent=2)+'\n',encoding='utf-8')
        meta['negative_witness_size']=len(witness)
    reports.append(meta);print(json.dumps(meta),flush=True)
    (r/'clock-cubic-large.json').write_text(json.dumps({'controls':controls,'reports':reports,
      'negative_found':negative is not None,'python':platform.python_version(),
      'Lean_verified':False,'uniform_cubic_decoder_proved':False,'canonical_observer_refuted':False,
      'full_problem_solved':False,'seconds':round(time.monotonic()-START,3)},indent=2)+'\n',encoding='utf-8')
    del mat
    if negative:break
