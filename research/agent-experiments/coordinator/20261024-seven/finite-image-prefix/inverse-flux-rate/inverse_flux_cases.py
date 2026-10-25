"""Owned universal inverse-column flux search, with actual model metadata."""
import argparse,hashlib,json,time
from pathlib import Path
from inverse_clock_flux_rate import synth

def main():
 p=argparse.ArgumentParser();p.add_argument('--columns',type=int,required=True);p.add_argument('--memory',type=int,required=True);p.add_argument('--domain',choices=['all','no00','golden','badclass'],required=True);p.add_argument('--factor',type=int,default=4);p.add_argument('--multiplier',type=int,default=1);p.add_argument('--clock',type=int,default=1);a=p.parse_args()
 started=time.monotonic();r=synth(columns=a.columns,memory=a.memory,domain=a.domain,factor=a.factor,seconds=90,spatial_multiplier=a.multiplier,clock=a.clock);r['total_seconds']=round(time.monotonic()-started,3)
 out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'records':[r],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 name='inverse-flux-rate-c'+str(a.columns)+'-k'+str(a.memory)+'-'+a.domain+'-F'+str(a.factor)+'-M'+str(a.multiplier)+'-clock'+str(a.clock)+'.json';(Path(__file__).resolve().parent/name).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print({k:v for k,v in r.items() if k not in ['certificate','reader_words','transition_table']},flush=True)
if __name__=='__main__':main()
