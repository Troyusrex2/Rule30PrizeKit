"""Prepare order-preserving actual-coupling examples for a recurrent rank reader."""
import hashlib,json,random
import numpy as np
from core import HERE
from regular_prefix_bothzero_rank_terminal import trajectory

def main():
 rng=random.Random(302521)
 structured=[0,1,2,3,5,17,31,495]+[1<<k for k in [2,3,7,15,31,63]]+[(1<<k)-1 for k in [2,3,7,15,31,63]]
 initials=structured+[rng.getrandbits(rng.randrange(8,129)) for _ in range(48)]
 train=[e for R in initials for e in trajectory(R,128,6)]
 held=[e for R in [0,1,2,31,495]+[rng.getrandbits(256) for _ in range(8)] for e in trajectory(R,512,256)]
 phases=sorted({r for e in train+held for r in e[2:4]});ix={r:i for i,r in enumerate(phases)};arrays={}
 for name,edges in [('train',train),('held',held)]:
  L=max(len(e[1]) for e in edges);before=np.full((len(edges),L),4,dtype=np.uint8);after=before.copy()
  for j,e in enumerate(edges):before[j,:len(e[0])]=e[0];after[j,:len(e[1])]=e[1]
  arrays.update({name+'_before':before,name+'_after':after,name+'_before_phase':np.array([ix[e[2]] for e in edges],dtype=np.int64),name+'_after_phase':np.array([ix[e[3]] for e in edges],dtype=np.int64),name+'_reward':np.array([e[4] for e in edges],dtype=np.float32)})
 out=HERE/'order-reader-data';out.mkdir(exist_ok=True)
 (out/'README.md').write_text('# Actual coupled rank-reader data\n\nRaw ordered two-bit anti-diagonal words; padding token4. Only transitions with both new spatial coordinates white. Actual driven-right dynamics, independent decoder controls; finite training and longer held-out samples are not a universal proof.\n',encoding='utf-8')
 np.savez_compressed(out/'actual-bothzero-ordered.npz',**arrays)
 names=['regular_prefix_bothzero_rank_terminal.py','charge_beam_packed.py','empty_right_absorption.py','coupled_even_code_probe.py']
 meta={'phases':phases,'train_examples':len(train),'held_examples':len(held),'training_depths':[6,127],'heldout_depths':[256,511],
  'data_sha256':hashlib.sha256((out/'actual-bothzero-ordered.npz').read_bytes()).hexdigest(),'producer_sources':{n:hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in names},
  'raw_order_preserved':True,'both_spatial_zero_edges':True,'actual_right_dynamics':True,'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
 (out/'data-manifest.json').write_text(json.dumps(meta,indent=2)+'\n',encoding='utf-8');print({k:v for k,v in meta.items() if k not in ['producer_sources','phases']},flush=True)
if __name__=='__main__':main()
