"""Counterexample-guided terminal reader refinement with a fresh test set."""
import hashlib,json,random,shutil
from pathlib import Path
import numpy as np
from regular_prefix_bothzero_rank_terminal import trajectory

ROOT=Path(__file__).resolve().parent;OUT=ROOT/'ordered-reader-v3'
OUT.mkdir(exist_ok=True)
old=np.load(ROOT/'order-reader-data/actual-bothzero-ordered.npz')
meta=json.loads((ROOT/'order-reader-data/data-manifest.json').read_text());phases=meta['phases'];ix={v:i for i,v in enumerate(phases)}
arrays={}
L=max(old['train_before'].shape[1],old['held_before'].shape[1])
for k in ['before','after','before_phase','after_phase','reward']:
 pieces=[old[n+'_'+k] for n in ['train','held']]
 if k in ['before','after']:pieces=[np.pad(x,((0,0),(0,L-x.shape[1])),constant_values=4) for x in pieces]
 arrays['train_'+k]=np.concatenate(pieces)
rng=random.Random(302540);seeds={}
for name,N,minimum,count,bits in [('held',1024,512,16,384),('test',2048,1024,8,512)]:
 initials=[rng.getrandbits(bits) for _ in range(count)];seeds[name]=[hex(x) for x in initials]
 edges=[e for initial in initials for e in trajectory(initial,N,minimum)];width=max(len(e[1]) for e in edges)
 before=np.full((len(edges),width),4,dtype=np.uint8);after=before.copy()
 for j,e in enumerate(edges):before[j,:len(e[0])]=e[0];after[j,:len(e[1])]=e[1]
 arrays.update({name+'_before':before,name+'_after':after,name+'_before_phase':np.array([ix[e[2]] for e in edges],dtype=np.int64),name+'_after_phase':np.array([ix[e[3]] for e in edges],dtype=np.int64),name+'_reward':np.array([e[4] for e in edges],dtype=np.float32)})
np.savez_compressed(OUT/'actual-bothzero-ordered.npz',**arrays)
newmeta={'version':3,'phases':phases,'train_examples':len(arrays['train_reward']),'held_examples':len(arrays['held_reward']),'test_examples':len(arrays['test_reward']),
 'training_depths':[6,511],'heldout_depths':[512,1023],'test_depths':[1024,2047],'baseline_validation_moved_to_training':True,'new_seed_random_generator':302540,'new_mathematical_seeds':seeds,
 'data_sha256':hashlib.sha256((OUT/'actual-bothzero-ordered.npz').read_bytes()).hexdigest(),'old_data_sha256':meta['data_sha256'],'producer_sources':meta['producer_sources'],
 'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'raw_order_preserved':True,'actual_right_dynamics':True,'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
(OUT/'data-manifest.json').write_text(json.dumps(newmeta,indent=2)+'\n',encoding='utf-8')
source=(ROOT/'ordered-reader-v2/train_ordered_rank_reader.py').read_text(encoding='utf-8')
source=source.replace("model=Reader(len(manifest['phases']),a.architecture).to(device);opt=torch.optim.Adam(model.parameters(),lr=.002)",
 "model=Reader(len(manifest['phases']),a.architecture).to(device)\n weight=root/'warmstart'/('v2-'+a.architecture+'-reader-weights.pt')\n assert weight.is_file()\n model.load_state_dict(torch.load(weight,map_location=device,weights_only=True));opt=torch.optim.Adam(model.parameters(),lr=.0005)")
source=source.replace("'version':2", "'version':3,'warmstart_weight_sha256':hashlib.sha256(weight.read_bytes()).hexdigest()")
source=source.replace("'checkpoint_selection':'training only'", "'checkpoint_selection':'training only; V2 validation moved to training; fresh held and test seeds'")
source=source.replace("root/'results';out.mkdir(exist_ok=True)", "root/'results';out.mkdir(exist_ok=True)")
(OUT/'train_ordered_rank_reader.py').write_text(source,encoding='utf-8',newline='\n')
for n in ['validate_ordered_reader_v2.py','guard_order_reader_v3_remote.py','audit_ordered_reader_v3.py']:
 shutil.copyfile(ROOT/n,OUT/n)
(OUT/'OWNER.txt').write_text('Rule30 terminal-aware ordered rank reader v3; 2026-10-25\n',encoding='utf-8')
(OUT/'README.md').write_text('''# Counterexample-guided terminal reader V3

The V2 ReLU reader satisfied all 2030 training inequalities but failed 14/693
longer validation inequalities in CPU double precision. It is not a rank.
V3 adds all old validation to training and starts from V2 weights. Selection
uses training only. Fresh held-out seeds have depths 512..1023, and a separate
test set has new seeds at depths 1024..2047. Test data are not read by training.
The final audit reports all failures and order reversal; no finite fit is a
proof. The .npz contains mathematical examples, not machine configuration.
''',encoding='utf-8')
names=['train_ordered_rank_reader.py','validate_ordered_reader_v2.py','guard_order_reader_v3_remote.py','audit_ordered_reader_v3.py','actual-bothzero-ordered.npz','data-manifest.json']
(OUT/'sources.json').write_text(json.dumps({n:hashlib.sha256((OUT/n).read_bytes()).hexdigest() for n in names},indent=2)+'\n',encoding='utf-8')
print({k:newmeta[k] for k in ['train_examples','held_examples','test_examples','data_sha256']},flush=True)
