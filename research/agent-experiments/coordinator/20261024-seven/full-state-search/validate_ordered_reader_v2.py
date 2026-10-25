"""Check padding and demonstrate that the revised family avoids the barrier."""
import hashlib,json
from pathlib import Path
import torch
from train_ordered_rank_reader import Reader

root=Path(__file__).resolve().parent
torch.manual_seed(302538)
records=[]
for architecture in ['relu','gru']:
 model=Reader(2,architecture).cpu().double().eval()
 words=torch.tensor([[1,2,4,4],[3,0,2,1],[4,4,4,4]],dtype=torch.long)
 phases=torch.tensor([0,1,0])
 with torch.no_grad():
  energy=model(words,phases)
  padded=model(torch.nn.functional.pad(words,(0,19),value=4),phases)
  assert torch.isfinite(energy).all() and (energy>=0).all()
  error=float((energy-padded).abs().max());assert error<1e-12,error
  records.append({'architecture':architecture,'nonnegative':True,'empty_supported':True,'padding_max_error':error})

# Construct a scalar terminal readout with E([1])=1 and E([1,0])=0.
# Prefix costs and constant are exactly zero; the active hidden first
# coordinate is 1 on token1 and 0 on token0. This is an exact CPU double test
# of the family, separate from the optimization experiment.
model=Reader(1,'relu').cpu().double().eval()
with torch.no_grad():
 for p in model.parameters():p.zero_()
 model.embed.weight[1,0]=1
 model.scan.weight_ih_l0[0,0]=1
 model.terminal_head.weight[0,0]=1
 a=model(torch.tensor([[1]]),torch.tensor([0])).item()
 b=model(torch.tensor([[1,0]]),torch.tensor([0])).item()
 assert a==1 and b==0,(a,b)
report={'reader_source_sha256':hashlib.sha256((root/'train_ordered_rank_reader.py').read_bytes()).hexdigest(),'padding_and_nonnegativity_controls':records,'explicit_nonmonotone_extension':{'short':[1],'long':[1,0],'short_energy':a,'long_energy':b},'uniform_rank_proved':False,'full_problem_solved':False}
(root/'architecture-controls.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report,flush=True)
