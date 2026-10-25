"""All two-state post-center readers on exact unbounded-radius folded rows.

A distinguished initial state consumes the center3, then the two-state
machine reads radial pairs. Native zero reward is not a Lean impossibility
proof. Unknown statuses are retained; positive results require exact rows.
"""
import argparse,collections,hashlib,time
from pathlib import Path
import numpy as np
from core import save
from universal_folded_row_rank import synth

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=165);a=p.parse_args();start=time.monotonic();records=[];complete=True
 for code in range(256):
  T=np.ones((3,4),dtype=np.int16)
  for state in range(2):
   for x in range(4):T[state+1,x]=1+((code>>(4*state+x))&1)
  r=synth(T,seconds=10);r['code']=code;records.append(r)
  if (code+1)%16==0 or r.get('exact_rational_graph_certificate'):
   save('folded-two-state-readers.json',{'enumerator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'helper_sha256':hashlib.sha256((Path(__file__).resolve().parent/'universal_folded_row_rank.py').read_bytes()).hexdigest(),'next_code':code+1,'complete':code==255,'post_center_states':2,'arbitrary_input_radius':True,'records':records,'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)})
   print({'next_code':code+1,'status_counts':dict(collections.Counter(x['solver_status'] for x in records)),'positive_exact_candidates':sum(x.get('exact_rational_graph_certificate',False) for x in records),'seconds':round(time.monotonic()-start,3)},flush=True)
  if r.get('exact_rational_graph_certificate') or time.monotonic()-start>a.seconds:complete=code==255;break
 save('folded-two-state-readers.json',{'enumerator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'helper_sha256':hashlib.sha256((Path(__file__).resolve().parent/'universal_folded_row_rank.py').read_bytes()).hexdigest(),'next_code':len(records),'complete':complete,'post_center_states':2,'arbitrary_input_radius':True,'records':records,'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)})
if __name__=='__main__':main()
