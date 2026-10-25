"""Owned finite-past sparse defect search; numerical outcomes are not proofs."""
import argparse,hashlib,json,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from left_finite_history_rank import synth

def main():
 p=argparse.ArgumentParser();p.add_argument('--reader',choices=['zero','last3','vacuum'],required=True);p.add_argument('--horizon',type=int,required=True);p.add_argument('--scale',default='1');p.add_argument('--depth',type=int,required=True);a=p.parse_args()
 if a.reader=='vacuum':
  from left_periodic_reader import build
  T,states,sink,controls=build()
 elif a.reader=='last3':T=np.array([[((q<<1)|x)&7 for x in range(2)] for q in range(8)],dtype=np.int16);controls={'reader':'last3'}
 else:T=np.zeros((1,2),dtype=np.int16);controls={'reader':'zero'}
 started=time.monotonic();r=synth(T,Fraction(a.scale),seconds=90,lookahead=a.horizon,depth=a.depth);r['seconds']=round(time.monotonic()-started,3)
 result={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'reader':controls,'records':[r],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 name='finite-history-d'+str(a.depth)+'-'+a.reader+'-H'+str(a.horizon)+'-scale'+a.scale.replace('/','-')+'.json';(Path(__file__).resolve().parent/name).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
if __name__=='__main__':main()
