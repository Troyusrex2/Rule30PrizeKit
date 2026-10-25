"""Resumable exhaustive two-state reader search; each file owns one code range."""
import argparse,hashlib,json,time
from pathlib import Path
import numpy as np
from universal_spatial_reader import synth

def main():
 p=argparse.ArgumentParser();p.add_argument('--start',type=int,required=True);p.add_argument('--end',type=int,required=True);p.add_argument('--seconds',type=float,default=210);a=p.parse_args()
 assert 0<=a.start<a.end<=65536;root=Path(__file__).resolve().parent;out=root/'results';out.mkdir(exist_ok=True)
 hashes={n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in ['universal_spatial_reader.py','enumerate_two_state_readers.py']}
 target=out/f'two-state-{a.start:05d}-{a.end:05d}.json'
 state={'range':[a.start,a.end],'source_sha256':hashes,'next_code':a.start,'status_counts':{},'unknown_codes':[],'numerical_feasible_codes':[],'exact_candidate_codes':[],
        'arbitrary_lengths_encoded_by_product_graphs':True,'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False,'seconds_accumulated':0.0}
 if target.exists():
  old=json.loads(target.read_text());assert old['range']==state['range'] and old['source_sha256']==hashes;state=old
 elif (root/'seed-manifest.json').exists():
  seeds=json.loads((root/'seed-manifest.json').read_text());name=target.name
  if name in seeds['files']:
   raw=(root/'seed-results'/name).read_bytes();assert hashlib.sha256(raw).hexdigest()==seeds['files'][name]
   old=json.loads(raw);assert old['range']==state['range']
   assert old['source_sha256']['universal_spatial_reader.py']==hashes['universal_spatial_reader.py']
   assert old['source_sha256']==seeds['predecessor_source_sha256']
   predecessor={'filename':name,'sha256':seeds['files'][name],'source_sha256':old['source_sha256'],'next_code':old['next_code']}
   state=old;state['source_sha256']=hashes;state['predecessor_checkpoint']=predecessor
 state['checkpoint_policy']='atomic replace with bounded Windows sharing retries'
 begin=time.monotonic();previous_seconds=state['seconds_accumulated'];processed=0
 def checkpoint():
  state['seconds_accumulated']=round(previous_seconds+time.monotonic()-begin,3);state['complete']=state['next_code']==a.end
  temp=target.with_suffix('.tmp');temp.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
  for attempt in range(100):
   try:temp.replace(target);break
   except PermissionError:
    if attempt==99:raise
    time.sleep(min(0.01*(attempt+1),0.25))
 for code in range(state['next_code'],a.end):
  if list(out.glob('candidate-*.json')):break
  T=np.array([[(code>>(8*p+s))&1 for s in range(8)] for p in range(2)],dtype=np.int16)
  rec=synth(T,seconds=5);status=str(rec['solver_status']);state['status_counts'][status]=state['status_counts'].get(status,0)+1
  if rec['solver_status'] not in [0,2]:state['unknown_codes'].append(code)
  if rec['solver_status']==0:state['numerical_feasible_codes'].append(code)
  if rec.get('exact_rational_graph_certificate'):
   state['exact_candidate_codes'].append(code);(out/f'candidate-{code:05d}.json').write_text(json.dumps({'code':code,'source_sha256':hashes,'record':rec},indent=2)+'\n',encoding='utf-8')
  state['next_code']=code+1;processed+=1
  if processed%64==0:checkpoint();print({'range_start':a.start,'next_code':state['next_code'],'statuses':state['status_counts']},flush=True)
  if state['exact_candidate_codes'] or time.monotonic()-begin>a.seconds:break
 checkpoint();print({'range':state['range'],'next_code':state['next_code'],'complete':state['complete'],'statuses':state['status_counts'],'elapsed_this_run':round(time.monotonic()-begin,3)},flush=True)
if __name__=='__main__':main()
