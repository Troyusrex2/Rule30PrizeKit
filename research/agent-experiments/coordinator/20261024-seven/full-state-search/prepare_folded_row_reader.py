"""Actual finite configurations, not anti-diagonal proxies, for a rank reader."""
import hashlib,json,random,shutil
from pathlib import Path
import numpy as np
from charge_beam_packed import step
from empty_right_absorption import step as right_driven
from universal_folded_row_rank import updated
ROOT=Path(__file__).resolve().parent;OUT=ROOT/'folded-row-reader';OUT.mkdir(exist_ok=True)

def evolve(L,c,R):return (L>>1)^(L|(L<<1)|c),(L&1)^(c|(R&1)),((R<<1)|c)^(R|(R>>1))
def folded(L,c,R):
 assert c==1
 return [3]+[((L>>j)&1)+2*((R>>j)&1) for j in range(max(L.bit_length(),R.bit_length()))]
def initial_left(R,N):
 x=R;row=old=spatial=0
 for d in range(N):
  x=right_driven(x,2*d);s=1^(x&1);x=right_driven(x,2*d+1)
  row,old=step(row,old,2*d,1);spatial|=((row>>(2*d))&1)<<(2*d)
  row,old=step(row,old,2*d+1,s);spatial|=((row>>(2*d+1))&1)<<(2*d+1)
 return spatial
def trajectory(R,N):
 L=initial_left(R,N);c=1;edges=[]
 for t in range(N):
  before=folded(L,c,R);l0,c0,r0=L,c,R
  L,c,R=evolve(L,c,R);assert c==0
  L,c,R=evolve(L,c,R);assert c==1
  after=folded(L,c,R);assert len(after)==len(before)+2
  if t in [0,N//2,N-1]:assert updated(before)==after
  edges.append((before,after))
 return edges

def controls():
 rng=random.Random(302550);count=0
 for _ in range(16):
  L=rng.getrandbits(12);R=rng.getrandbits(12);c=rng.randrange(2);row={0:c,**{-j-1:(L>>j)&1 for j in range(12)},**{j+1:(R>>j)&1 for j in range(12)}}
  for t in range(12):
   old=row;row={p:(30>>((old.get(p-1,0)<<2)|(old.get(p,0)<<1)|old.get(p+1,0)))&1 for p in range(-13-t,14+t)};L,c,R=evolve(L,c,R)
   assert row[0]==c
   for j in range(13+t):assert row[-j-1]==((L>>j)&1) and row[j+1]==((R>>j)&1);count+=2
 return count

def main():
 independent=controls();rng=random.Random(302551);structured=[0,1,2,3,17,31,495]+[rng.getrandbits(64) for _ in range(5)];sets={};seeds={}
 sets['train']=[e for R in structured for N in [16,24,32,48,64] for e in trajectory(R,N)];seeds['train']=[hex(x) for x in structured]
 for part,N,bits in [('held',128,128),('test',256,256)]:
  initials=[rng.getrandbits(bits) for _ in range(8)];seeds[part]=[hex(x) for x in initials];sets[part]=[e for R in initials for e in trajectory(R,N)]
 arrays={}
 for part,edges in sets.items():
  width=max(len(e[1]) for e in edges);before=np.full((len(edges),width),4,dtype=np.uint8);after=before.copy()
  for j,(x,y) in enumerate(edges):before[j,:len(x)]=x;after[j,:len(y)]=y
  arrays.update({part+'_before':before,part+'_after':after,part+'_before_phase':np.zeros(len(edges),dtype=np.int64),part+'_after_phase':np.zeros(len(edges),dtype=np.int64),part+'_reward':np.ones(len(edges),dtype=np.float32)})
 np.savez_compressed(OUT/'actual-bothzero-ordered.npz',**arrays)
 meta={'task':'nonnegative rank on complete finite spatial configurations read from center outward','phases':[0],'train_examples':len(sets['train']),'held_examples':len(sets['held']),'test_examples':len(sets['test']),'initial_left_widths':{'train':[32,48,64,96,128],'held':[256],'test':[512]},'right_seed_bits':{'train':64,'held':128,'test':256},'mathematical_right_seeds':seeds,'actual_two_step_center_1_to_0_to_1':True,'both_finite_halves_retained':True,'new_test_right_seeds':True,'independent_truth_table_cells':independent,'folded_transducer_controls_per_trace':3,'data_sha256':hashlib.sha256((OUT/'actual-bothzero-ordered.npz').read_bytes()).hexdigest(),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'producer_sources':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in ['charge_beam_packed.py','empty_right_absorption.py','universal_folded_row_rank.py']},'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
 (OUT/'data-manifest.json').write_text(json.dumps(meta,indent=2)+'\n',encoding='utf-8')
 source=(ROOT/'ordered-reader-v2/train_ordered_rank_reader.py').read_text(encoding='utf-8').replace("'version':2", "'version':'folded-full-spatial-row-v1'")
 source=source.replace('Learn an order-sensitive nonnegative rank on actual both-white transitions.',
  'Learn a nonnegative rank on full center-out finite spatial configurations.')
 (OUT/'train_ordered_rank_reader.py').write_text(source,encoding='utf-8',newline='\n')
 for n in ['validate_ordered_reader_v2.py','audit_ordered_reader_v3.py','guard_folded_row_reader.py']:shutil.copyfile(ROOT/n,OUT/n)
 (OUT/'OWNER.txt').write_text('Rule30 full folded spatial row reader; 2026-10-25\n',encoding='utf-8')
 (OUT/'README.md').write_text('''# Full finite configurations read from the center outward

This changes the task from inverse anti-diagonals to complete physical
spatial configurations. Every before and after word retains both finite
halves, paired at equal distance from a black center. The actual center
flips 1->0->1; reward is one per double step. Initial left halves are finite
prefixes of Psi(R), so controlled finite runs exist. No infinite-support
configuration is used. Train left widths32..128; validation256; test512.
Validation and test have fresh mathematical right seeds. Packed physical
evolution was checked against literal Rule30 truth tables and three exact
folded-transducer checks per trace. A finite fit is never a universal rank.
The retained NPZ filename is an inherited training interface, not a claim
that these are the earlier both-white anti-diagonal edges. Selection is
training only; CPU double precision and untouched deep tests are required.
''',encoding='utf-8')
 names=['train_ordered_rank_reader.py','validate_ordered_reader_v2.py','audit_ordered_reader_v3.py','guard_folded_row_reader.py','actual-bothzero-ordered.npz','data-manifest.json']
 (OUT/'sources.json').write_text(json.dumps({n:hashlib.sha256((OUT/n).read_bytes()).hexdigest() for n in names},indent=2)+'\n',encoding='utf-8');print({k:meta[k] for k in ['train_examples','held_examples','test_examples','independent_truth_table_cells','data_sha256']},flush=True)
if __name__=='__main__':main()
