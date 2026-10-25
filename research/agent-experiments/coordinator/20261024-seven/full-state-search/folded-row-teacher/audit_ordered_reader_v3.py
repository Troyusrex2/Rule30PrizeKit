"""Independent CPU-double audit including the untouched longer test set."""
import argparse,hashlib,json
from pathlib import Path
import numpy as np
import torch
from train_ordered_rank_reader import Reader

def main():
 p=argparse.ArgumentParser();p.add_argument('--architecture',default='relu');a=p.parse_args();torch.set_num_threads(4)
 root=Path(__file__).resolve().parent;meta=json.loads((root/'data-manifest.json').read_text());data=np.load(root/'actual-bothzero-ordered.npz')
 weight=root/'results'/(a.architecture+'-reader-weights.pt');model=Reader(len(meta['phases']),a.architecture).cpu().double().eval()
 model.load_state_dict(torch.load(weight,map_location='cpu',weights_only=True))
 report={'architecture':a.architecture,'data_sha256':hashlib.sha256((root/'actual-bothzero-ordered.npz').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'weight_sha256':hashlib.sha256(weight.read_bytes()).hexdigest(),'sets':{},'finite_test_only':True,'uniform_rank_proved':False,'full_problem_solved':False}
 assert report['data_sha256']==meta['data_sha256']
 with torch.no_grad():
  for part in ['train','held','test']:
   failures=[];maximum=-float('inf');nonfinite=0
   for start in range(0,len(data[part+'_reward']),32):
    end=min(start+32,len(data[part+'_reward']));words=torch.tensor(np.concatenate([data[part+'_before'][start:end],data[part+'_after'][start:end]]),dtype=torch.long)
    phase=torch.tensor(np.concatenate([data[part+'_before_phase'][start:end],data[part+'_after_phase'][start:end]]),dtype=torch.long)
    v=model(words,phase);n=end-start;r=v[n:]-v[:n]+torch.tensor(data[part+'_reward'][start:end],dtype=torch.float64)
    nonfinite+=int((~torch.isfinite(r)).sum());maximum=max(maximum,float(r.max()))
    for j in torch.where(r>1e-6)[0].tolist():
     i=start+j;failures.append({'index':i,'residual':float(r[j]),'before_length':int((data[part+'_before'][i]!=4).sum()),'reward':int(data[part+'_reward'][i]),'before_phase':meta['phases'][int(data[part+'_before_phase'][i])],'after_phase':meta['phases'][int(data[part+'_after_phase'][i])]})
   report['sets'][part]={'examples':len(data[part+'_reward']),'violations_1e6':len(failures),'maximum_residual':maximum,'nonfinite':nonfinite,'failures':failures}
 target=root/'results'/(a.architecture+'-independent-test-audit.json');target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
 print({'architecture':a.architecture,'sets':{p:{k:v for k,v in r.items() if k!='failures'} for p,r in report['sets'].items()}},flush=True)
if __name__=='__main__':main()
