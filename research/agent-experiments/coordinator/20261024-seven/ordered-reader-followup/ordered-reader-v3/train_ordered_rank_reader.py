"""Learn an order-sensitive nonnegative rank on actual both-white transitions.

This is numerical discovery. The recurrent reader shares weights across all
lengths; its energy sums squared prefix readouts and a squared terminal readout.
The terminal readout avoids the independently verified prefix-monotone barrier.
Longer held-out rows and a float64 reevaluation are mandatory. No learned
network is accepted as a universal proof.
"""
import argparse,copy,hashlib,json,math,time
from pathlib import Path
import numpy as np
import torch
from torch import nn

class Reader(nn.Module):
 def __init__(self,phases,architecture):
  super().__init__();self.embed=nn.Embedding(5,8,padding_idx=4)
  self.scan=nn.RNN(8,32,batch_first=True,nonlinearity='relu') if architecture=='relu' else nn.GRU(8,32,batch_first=True)
  self.head=nn.Embedding(phases,32);self.bias=nn.Embedding(phases,1);self.constant=nn.Embedding(phases,1)
  self.terminal_head=nn.Embedding(phases,32);self.terminal_bias=nn.Embedding(phases,1)
  nn.init.normal_(self.terminal_head.weight,0,.03);nn.init.constant_(self.terminal_bias.weight,1.0)
  nn.init.normal_(self.head.weight,0,.03);nn.init.constant_(self.bias.weight,.1);nn.init.constant_(self.constant.weight,.1)
  if architecture=='relu':
   with torch.no_grad():self.scan.weight_hh_l0.copy_(torch.eye(32)*.8);self.scan.bias_hh_l0.zero_();self.scan.bias_ih_l0.fill_(.02)
 def forward(self,words,phase):
  h,_=self.scan(self.embed(words));score=(h*self.head(phase)[:,None,:]).sum(-1)+self.bias(phase)
  lengths=(words!=4).sum(-1)
  last=h[torch.arange(len(words),device=words.device),(lengths-1).clamp_min(0)]
  terminal=(last*self.terminal_head(phase)).sum(-1)+self.terminal_bias(phase).flatten()
  terminal=terminal.square()*(lengths>0)
  return (score.square()*(words!=4)).sum(-1)+self.constant(phase).flatten().square()+terminal

def main():
 p=argparse.ArgumentParser();p.add_argument('--architecture',choices=['relu','gru'],default='relu');p.add_argument('--seconds',type=float,default=165);p.add_argument('--epochs',type=int,default=4000);p.add_argument('--seed',type=int,default=302536);a=p.parse_args()
 root=Path(__file__).resolve().parent;manifest=json.loads((root/'data-manifest.json').read_text());datafile=root/'actual-bothzero-ordered.npz'
 assert hashlib.sha256(datafile.read_bytes()).hexdigest()==manifest['data_sha256'];assert torch.cuda.is_available()
 torch.set_num_threads(4);torch.manual_seed(a.seed);np.random.seed(a.seed);device=torch.device('cuda');free,total=torch.cuda.mem_get_info();assert free>3*(1024**3)
 data=np.load(datafile);sets={}
 for name in ['train','held']:
  sets[name]={k:torch.tensor(data[name+'_'+k],dtype=torch.long if k!='reward' else torch.float32,device=device) for k in ['before','after','before_phase','after_phase','reward']}
 model=Reader(len(manifest['phases']),a.architecture).to(device)
 weight=root/'warmstart'/('v2-'+a.architecture+'-reader-weights.pt')
 assert weight.is_file()
 model.load_state_dict(torch.load(weight,map_location=device,weights_only=True));opt=torch.optim.Adam(model.parameters(),lr=.0005)
 start=time.monotonic();records=[];bestkey=None;best=None;steps=0
 def residual(part,ids=None):
  d=sets[part]
  if ids is None:ids=torch.arange(len(d['reward']),device=device)
  words=torch.cat([d['before'][ids],d['after'][ids]]);phases=torch.cat([d['before_phase'][ids],d['after_phase'][ids]])
  values=model(words,phases);n=len(ids);return values[n:]-values[:n]+d['reward'][ids],values
 @torch.no_grad()
 def evaluate(part):
  rr=[]
  for ids in torch.arange(len(sets[part]['reward']),device=device).split(64):rr.append(residual(part,ids)[0].detach().cpu())
  r=torch.cat(rr);return {'violations_1e4':int((r>1e-4).sum()),'maximum_residual':float(r.max()),'nonfinite':int((~torch.isfinite(r)).sum())}
 for epoch in range(a.epochs):
  model.train();losses=[];order=torch.randperm(len(sets['train']['reward']),device=device)
  for ids in order.split(128):
   if time.monotonic()-start>a.seconds:break
   opt.zero_grad();r,v=residual('train',ids);loss=torch.relu(r).square().mean()+1e-8*v.mean()
   if not torch.isfinite(loss):raise RuntimeError('Nonfinite recurrent training loss; no candidate')
   loss.backward();torch.nn.utils.clip_grad_norm_(model.parameters(),5);opt.step();steps+=1;losses.append(float(loss.detach()))
   if a.architecture=='relu' and steps%10==0:
    with torch.no_grad():
     w=model.scan.weight_hh_l0;s=torch.linalg.svdvals(w)[0];w.mul_(torch.clamp(1.01/s,max=1.0))
  if epoch%5==0 or time.monotonic()-start>a.seconds:
   model.eval();tr=evaluate('train');he=evaluate('held');rec={'epoch':epoch,'loss':float(np.mean(losses)) if losses else None,'train':tr,'held':he,'seconds':round(time.monotonic()-start,3)};records.append(rec);print(rec,flush=True)
   key=(tr['nonfinite'],tr['violations_1e4'],tr['maximum_residual'])
   if bestkey is None or key<bestkey:bestkey=key;best={k:v.detach().cpu().clone() for k,v in model.state_dict().items()}
   if not tr['nonfinite'] and not he['nonfinite'] and not tr['violations_1e4'] and not he['violations_1e4']:break
  if time.monotonic()-start>a.seconds:break
 assert best is not None;model.load_state_dict(best);model=model.cpu().double().eval()
 def cpu_eval(part,reverse=False):
  d={k:torch.tensor(data[part+'_'+k],dtype=torch.long if k!='reward' else torch.float64) for k in ['before','after','before_phase','after_phase','reward']};res=[]
  with torch.no_grad():
   for ids in torch.arange(len(d['reward'])).split(64):
    words=torch.cat([d['before'][ids],d['after'][ids]])
    if reverse:
     words=words.clone()
     for row in words:
      n=int((row!=4).sum());row[:n]=row[:n].flip(0)
    vals=model(words,torch.cat([d['before_phase'][ids],d['after_phase'][ids]]));n=len(ids);res.append(vals[n:]-vals[:n]+d['reward'][ids])
  r=torch.cat(res);return {'violations_1e6':int((r>1e-6).sum()),'maximum_residual':float(r.max()),'nonfinite':int((~torch.isfinite(r)).sum())}
 finaltrain=cpu_eval('train');finalheld=cpu_eval('held');ablation=cpu_eval('held',True)
 # Check that padded token4 does not manufacture positive energy.
 with torch.no_grad():
  sample=torch.tensor(data['train_before'][:8],dtype=torch.long);phase=torch.tensor(data['train_before_phase'][:8],dtype=torch.long)
  padding_difference=float((model(sample,phase)-model(torch.nn.functional.pad(sample,(0,17),value=4),phase)).abs().max())
 out=root/'results';out.mkdir(exist_ok=True);weightfile=out/(a.architecture+'-reader-weights.pt');torch.save(best,weightfile)
 report={'architecture':a.architecture,'energy':'nonnegative phase constant squared plus sum of squared ordered prefix readouts plus squared word-dependent terminal readout','version':3,'warmstart_weight_sha256':hashlib.sha256(weight.read_bytes()).hexdigest(),'checkpoint_selection':'training only; V2 validation moved to training; fresh held and test seeds','seed':a.seed,'requested_epochs':a.epochs,'seconds_budget':a.seconds,'width_normalization':False,
  'data_sha256':manifest['data_sha256'],'data_manifest':manifest,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'torch_version':torch.__version__,'device':torch.cuda.get_device_name(0),
  'training_records':records,'best_selection_key':bestkey,'float64_training':finaltrain,'float64_heldout':finalheld,'reversed_token_ablation':ablation,'padding_invariance_max_error':padding_difference,
  'weight_sha256':hashlib.sha256(weightfile.read_bytes()).hexdigest(),'gpu_peak_allocated_gib':round(torch.cuda.max_memory_allocated()/1024**3,4),
  'seconds':round(time.monotonic()-start,3),'finite_fit_only':True,'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
 (out/(a.architecture+'-reader-report.json')).write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print({'architecture':a.architecture,'float64_train':finaltrain,'float64_held':finalheld,'padding_error':padding_difference,'seconds':report['seconds'],'uniform_rank_proved':False},flush=True)
if __name__=='__main__':main()
