"""Fit signed prefix energies selected by an upcoming-free-bit phase."""
import argparse,hashlib,json,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from left_future_history_strict_rank import synth

def main():
 p=argparse.ArgumentParser();p.add_argument('--reader',choices=['zero','last3','vacuum','multi'],required=True);p.add_argument('--memory',type=int,required=True);p.add_argument('--scale',default='1');p.add_argument('--depth',type=int,required=True);args=p.parse_args()
 if args.reader=='multi':
  from left_multi_vacuum_reader import build
  T,patterns,states,reader_control=build()
 elif args.reader=='vacuum':
  from left_periodic_reader import build
  T,states,sink,reader_control=build()
 elif args.reader=='last3':T=np.array([[((q<<1)|x)&7 for x in range(2)] for q in range(8)],dtype=np.int16);reader_control={'reader':'last3'}
 else:T=np.zeros((1,2),dtype=np.int16);reader_control={'reader':'zero'}
 started=time.monotonic();r=synth(T,Fraction(args.scale),seconds=600,lookahead=13,future_memory=args.memory,depth=args.depth);r['seconds']=round(time.monotonic()-started,3)
 result={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'reader':reader_control,'records':[r],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 name='future-history-strict-d'+str(args.depth)+'-'+args.reader+'-K'+str(args.memory)+'-scale'+args.scale.replace('/','-')+'.json';(Path(__file__).resolve().parent/name).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
if __name__=='__main__':main()
