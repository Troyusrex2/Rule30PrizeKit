"""Uniform slack search with an explicit transient initial reader state."""
import argparse,time
import numpy as np
from core import save
from universal_spatial_reader_slack import synth

def transient(T,first=None):
 k=len(T);U=np.empty((k+1,8),dtype=np.int16);U[0]=1+(T[0] if first is None else first);U[1:]=T+1;return U

def main():
 p=argparse.ArgumentParser();p.add_argument('--models',type=int,default=260);a=p.parse_args();rng=np.random.default_rng(302533);start=time.monotonic()
 graphs=[('nonempty',np.ones((2,8),dtype=np.int16)),('transient_last_symbol',transient(np.tile(np.arange(8,dtype=np.int16),(8,1))))]
 for mask in range(1,255):
  T=np.array([[s^((mask>>a)&1) for a in range(8)] for s in range(2)],dtype=np.int16);graphs.append(('transient_parity_'+str(mask),transient(T)))
 while len(graphs)<a.models:
  k=[3,4,6,8][len(graphs)%4];T=rng.integers(0,k,(k,8),dtype=np.int16);graphs.append(('transient_general',transient(T)))
 out={'transient_initial_state':True,'arbitrary_lengths_encoded_by_product_graphs':True,'records':[],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 for i,(kind,T) in enumerate(graphs[:a.models]):
  rec=synth(T);rec.update({'model':i,'kind':kind})
  if rec.get('epsilon',99)>0.21:rec.pop('certificate',None)
  out['records'].append(rec);out['seconds']=round(time.monotonic()-start,3);save('universal-spatial-reader-slack-structured.json',out)
  print({k:v for k,v in rec.items() if k not in ['certificate','transition_table']},flush=True)
  if rec.get('strict_density_margin_candidate') or rec.get('critical_density_candidate') or time.monotonic()-start>220:break
if __name__=='__main__':main()
