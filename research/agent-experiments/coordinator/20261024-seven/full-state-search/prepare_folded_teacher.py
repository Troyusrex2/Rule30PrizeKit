"""Measure actual finite lifetimes to supervise the full-configuration reader."""
import hashlib,json,shutil
from pathlib import Path
import numpy as np
from prepare_folded_row_reader import evolve,folded,initial_left,controls
from universal_folded_row_rank import updated
ROOT=Path(__file__).resolve().parent;OUT=ROOT/'folded-row-teacher';OUT.mkdir(exist_ok=True)

def trace(R,N):
 L=initial_left(R,N);c=1;edges=[];failed=False
 for t in range(16*N+128):
  before=folded(L,c,R);a,b,d=evolve(L,c,R)
  if b!=0:failed=True;break
  a,b,d=evolve(a,b,d)
  if b!=1:failed=True;break
  after=folded(a,b,d);edges.append((before,after));L,c,R=a,b,d
 assert failed,('Lifetime not established within bounded generator',N)
 assert len(edges)>=N
 for j in sorted({0,len(edges)//2,len(edges)-1}):assert updated(edges[j][0])==edges[j][1]
 return [(x,y,len(edges)-j,len(edges)-j-1) for j,(x,y) in enumerate(edges)]

def main():
 old=json.loads((ROOT/'folded-row-reader/data-manifest.json').read_text());sets={};witnesses=[]
 for part,Ns in [('train',[16,24,32,48,64]),('held',[128]),('test',[256])]:
  rows=[]
  for seed in old['mathematical_right_seeds'][part]:
   for N in Ns:
    edges=trace(int(seed,16),N);witnesses.append({'part':part,'right_seed':seed,'initial_left_width':2*N,'observed_good_double_steps':len(edges),'next_double_step_failed':True});rows+=edges
  sets[part]=rows
 consistent={}
 for rows in sets.values():
  for before,after,b,a in rows:
   for word,target in [(before,b),(after,a)]:
    key=tuple(word)
    if key in consistent:assert consistent[key]==target
    else:consistent[key]=target
 arrays={}
 for part,rows in sets.items():
  width=max(len(y) for x,y,b,a in rows);before=np.full((len(rows),width),4,dtype=np.uint8);after=before.copy()
  for j,(x,y,b,a) in enumerate(rows):before[j,:len(x)]=x;after[j,:len(y)]=y
  arrays.update({part+'_before':before,part+'_after':after,part+'_before_phase':np.zeros(len(rows),dtype=np.int64),part+'_after_phase':np.zeros(len(rows),dtype=np.int64),part+'_reward':np.ones(len(rows),dtype=np.float32),part+'_before_lifetime':np.array([r[2] for r in rows],dtype=np.float32),part+'_after_lifetime':np.array([r[3] for r in rows],dtype=np.float32)})
 np.savez_compressed(OUT/'actual-bothzero-ordered.npz',**arrays)
 meta={**old,'version':'folded-row-teacher-v1','train_examples':len(sets['train']),'held_examples':len(sets['held']),'test_examples':len(sets['test']),'data_sha256':hashlib.sha256((OUT/'actual-bothzero-ordered.npz').read_bytes()).hexdigest(),'predecessor_data_sha256':old['data_sha256'],'teacher':'actual number of complete 1->0->1 double steps before observed alternation failure','all_traces_failed_within_generator_bound':True,'lifetime_witnesses':witnesses,'same_word_lifetime_consistency_passed':True,'distinct_labeled_words':len(consistent),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'independent_truth_table_cells':controls()}
 (OUT/'data-manifest.json').write_text(json.dumps(meta,indent=2)+'\n',encoding='utf-8')
 s=(ROOT/'folded-row-reader/train_ordered_rank_reader.py').read_text(encoding='utf-8')
 s=s.replace("for k in ['before','after','before_phase','after_phase','reward']", "for k in ['before','after','before_phase','after_phase','reward','before_lifetime','after_lifetime']")
 s=s.replace("dtype=torch.long if k!='reward' else torch.float32", "dtype=torch.float32 if k in ('reward','before_lifetime','after_lifetime') else torch.long")
 s=s.replace("data=np.load(datafile);sets={}", "data=np.load(datafile);teacher_scale=float(np.max(data['train_before_lifetime']));assert teacher_scale>0;sets={}")
 oldloss="opt.zero_grad();r,v=residual('train',ids);loss=torch.relu(r).square().mean()+1e-8*v.mean()"
 newloss="""opt.zero_grad();r,v=residual('train',ids)
   target=torch.cat([sets['train']['before_lifetime'][ids],sets['train']['after_lifetime'][ids]])
   supervised=((v-target)/teacher_scale).square().mean()
   loss=supervised if time.monotonic()-start<45 else torch.relu(r).square().mean()+.1*supervised+1e-8*v.mean()"""
 assert oldloss in s;s=s.replace(oldloss,newloss)
 s=s.replace("if bestkey is None or key<bestkey:bestkey=key;", "if time.monotonic()-start>=45 and (bestkey is None or key<bestkey):bestkey=key;")
 s=s.replace("if not tr['nonfinite'] and not he['nonfinite'] and not tr['violations_1e4']", "if best is not None and not tr['nonfinite'] and not he['nonfinite'] and not tr['violations_1e4']")
 s=s.replace("'version':'folded-full-spatial-row-v1'", "'version':'folded-full-spatial-row-teacher-v1','teacher_pretraining_seconds':45,'teacher_scale':teacher_scale,'teacher_loss':'normalized squared actual lifetime error; 45s pretraining then hinge plus 0.1 teacher loss'")
 (OUT/'train_ordered_rank_reader.py').write_text(s,encoding='utf-8',newline='\n')
 for n in ['validate_ordered_reader_v2.py','audit_ordered_reader_v3.py']:shutil.copyfile(ROOT/n,OUT/n)
 s=(ROOT/'guard_folded_row_reader.py').read_text(encoding='utf-8').replace('Rule30 full folded spatial row reader; 2026-10-25','Rule30 supervised folded spatial row reader; 2026-10-25')
 (OUT/'guard_folded_row_reader.py').write_text(s,encoding='utf-8',newline='\n')
 (OUT/'OWNER.txt').write_text('Rule30 supervised folded spatial row reader; 2026-10-25\n',encoding='utf-8')
 (OUT/'README.md').write_text('''# Actual-lifetime supervision on full spatial configurations

Every generated finite run was continued until center alternation failed.
Labels are the observed remaining number of complete 1->0->1 double steps.
Repeated identical full words have consistent labels. No bounded simulation
timeout is called a termination. All initial cases from the previous full-row
dataset were retained, with the final good steps added. New right seeds are
reserved for validation and test. The same network initialization is used;
45s normalized lifetime supervision precedes the rank hinge objective.
Checkpoint selection and supervision use training only. Fresh test labels
are never read by training. Finite fitting cannot establish a universal rank.
The old sources and failed experiment records remain unchanged.
''',encoding='utf-8')
 names=['train_ordered_rank_reader.py','validate_ordered_reader_v2.py','audit_ordered_reader_v3.py','guard_folded_row_reader.py','actual-bothzero-ordered.npz','data-manifest.json']
 (OUT/'sources.json').write_text(json.dumps({n:hashlib.sha256((OUT/n).read_bytes()).hexdigest() for n in names},indent=2)+'\n',encoding='utf-8')
 print({k:meta[k] for k in ['train_examples','held_examples','test_examples','distinct_labeled_words','same_word_lifetime_consistency_passed','data_sha256']},flush=True)
if __name__=='__main__':main()
