"""Test full-state cycle closure, and search structured finite right halves."""
from pathlib import Path
import importlib.util,json,time
ROOT=Path(__file__).resolve().parent
source=ROOT/'snapshots/r30-coinailyzer-wiki-20261026T005537Z-e656e7b7-v01/src/coupled_core.py'
spec=importlib.util.spec_from_file_location('wiki_core',source);core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
L=94;cut=2*L;width=cut+4;mask=(1<<width)-1
def f(s):return (s+int(s>=L))%2
initial=sum((1 if t%2==0 else f(t//2))<<t for t in range(width))
def step(pair):
    older,current=pair
    shifted=(current>>1)|(((current>>cut)&1)<<(width-1))
    return current,(shifted^(current|older))&mask
pair=(0,initial);seen={};output=[0];cycle=None
for k in range(1,10001):
    if pair in seen:
        cycle={'entry_depth':seen[pair],'return_depth':k,'period':k-seen[pair],
               'state_bits_each':width,'entry_pair_hex':[hex(x) for x in pair]}
        break
    seen[pair]=k;output.append(pair[1]&1);pair=step(pair)
if cycle is not None:
    entry,period=cycle['entry_depth'],cycle['period']
    cycle['black_per_period']=sum(output[entry:entry+period])
    word=output[entry:entry+period]
    minimal=next(p for p in range(1,period+1) if period%p==0 and all(word[i]==word[i%p] for i in range(period)))
    cycle['output_period']=minimal
    cycle['output_black_per_period']=sum(word[:minimal])
    assert len(output)==cycle['return_depth']
direct=core.psi_row([f(s) for s in range(len(output)//2+3)],len(output)-1)
assert direct==output
# Equality of the entire pair is a real closed-state witness. A Lean bridge
# from this finite profile to the official recon is still required.

target=[f(s) for s in range(160)]
candidate_checks=0;prefix_hits=[];best={'matching_prefix':-1}
walls=[[1,0,1,1,0,1,0,1,1,0,0,0,0],
       [int(0x72270>>i&1) for i in range(19)],[],[1],[0,1],[1,1]]
started=time.monotonic()
for j in range(7):
 for phase in range(4):
  for k in range(0,201):
   for wi,wall in enumerate(walls):
    candidate_checks+=1
    seed=core.right_mask(core.config(j,phase,k,wall))
    observed=core.free_stream(seed,len(target))
    match=next((i for i,(a,b) in enumerate(zip(target,observed)) if a!=b),len(target))
    candidate={'matching_prefix':match,'j':j,'phase':phase,'ether_length':k,'wall_index':wi,'right_half_hex':hex(seed)}
    if match>best['matching_prefix']:best=candidate
    if match==len(target):prefix_hits.append(candidate)
    assert time.monotonic()-started<180
report={'full_profile_cycle':cycle,'profile_vs_original_prefix_equal':True,
        'finite_profile_is_closed':cycle is not None,'Lean_verified':False,
        'achievability_search':{'candidates':candidate_checks,'best':best,'prefix_hits':prefix_hits,
             'proof_of_no_finite_realization':False,'matched_bits':len(target)},
        'full_problem_solved':False}
(ROOT/'wiki-closed-profile.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
