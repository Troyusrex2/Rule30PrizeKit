"""Structured temporal readers on the wider, physically closed strip domain."""
import argparse,hashlib,time
from pathlib import Path
import numpy as np
from core import save
from universal_strip_energy import synth

def readers(M):
 A=1<<M
 for period in [2,4,5,7,10]:
  yield 'clock'+str(period),np.array([[(q+1)%period]*A for q in range(period)],dtype=np.int16)
  T=np.empty((period+1,A),dtype=np.int16);T[0,:]=1+(1%period)
  for q in range(period):T[q+1,:]=1+(q+1)%period
  yield 'transient_clock'+str(period),T
 T=np.tile(1+(np.arange(A)&7),(9,1)).astype(np.int16)
 yield 'transient_last_triple',T
 for period in [2,4]:
  T=np.empty((1+8*period,A),dtype=np.int16);T[0,:]=1+8*(1%period)+(np.arange(A)&7)
  for q in range(period):
   for last in range(8):T[1+8*q+last,:]=1+8*((q+1)%period)+(np.arange(A)&7)
  yield 'clock_last_triple'+str(period),T

def main():
 p=argparse.ArgumentParser();p.add_argument('--min-width',type=int,default=4);p.add_argument('--max-width',type=int,default=9);p.add_argument('--seconds',type=float,default=165);a=p.parse_args();start=time.monotonic();records=[]
 for M in range(a.min_width,a.max_width+1):
  for kind,T in readers(M):
   begin=time.monotonic();r=synth(M,T,seconds=20);r.update({'kind':kind,'seconds':round(time.monotonic()-begin,3)})
   if not r.get('useful_critical_candidate'):r.pop('certificate',None)
   records.append(r);save('universal-strip-structured.json',{'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'helper_sha256':hashlib.sha256((Path(__file__).resolve().parent/'universal_strip_energy.py').read_bytes()).hexdigest(),'arbitrary_lengths_encoded_by_product_graphs':True,'records':records,'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)})
   print({k:v for k,v in r.items() if k not in ['transition_table','certificate']},flush=True)
   if r.get('useful_critical_candidate') or time.monotonic()-start>a.seconds:return
if __name__=='__main__':main()
