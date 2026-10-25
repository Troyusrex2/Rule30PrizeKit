"""Resolve two recorded IPM failures using a separate dual-simplex run."""
import hashlib,time
from pathlib import Path
from fractions import Fraction as F
from core import save

def main():
 source=Path('folded_signed_geometric_rank.py').read_text(encoding='utf-8');assert source.count("method='highs-ipm'")==1
 source=source.replace("method='highs-ipm'","method='highs-ds'");target=Path('folded_signed_geometric_ds.py');target.write_text(source,encoding='utf-8',newline='\n')
 import folded_signed_geometric_ds as experiment
 name,T=list(experiment.readers())[-1];assert name=='joint_last_pairs3';out={'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'original_source_sha256':hashlib.sha256(Path('folded_signed_geometric_rank.py').read_bytes()).hexdigest(),'change':'solver highs-ipm to highs-ds only','records':[],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 for scale in [F(1),F(3)]:
  start=time.monotonic();r=experiment.synth(T,scale,seconds=60);r.update({'kind':name,'seconds':round(time.monotonic()-start,3)});out['records'].append(r);save('folded-signed-geometric-ds-retry.json',out);print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
if __name__=='__main__':main()
