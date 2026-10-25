"""Rebuild the five obstruction examples independently of packed training code."""
import json
from core import HERE,save
from zero_tail_rank import step as scalar_step

def truth(a,b,c):return (30>>((a<<2)|(b<<1)|c))&1

def main():
 d=json.loads((HERE/'bothzero-linear-obstruction.json').read_text());out=[]
 for e in d['certificate']['edges']:
  seed=int(e['initial_right_hex'],16);N=e['depth']+1;row={p:seed>>(p-1)&1 for p in range(1,max(1,seed.bit_length())+1)};free=[]
  for t in range(2*N):
   old={**row,0:1 if t%2==0 else 0};row={p:truth(old.get(p-1,0),old.get(p,0),old.get(p+1,0)) for p in range(1,max(row)+2)}
   if t%2==0:free.append(1^row[1])
  R=[];Rm=[];spatial=[]
  for k,s in enumerate(free):
   before=[1]+[sum((a+2*(Rm[j] if j<len(Rm) else 0))==v for j,a in enumerate(R)) for v in range(4)]
   R1,old=scalar_step(R,Rm,1);odd=R1[-1];R,Rm=scalar_step(R1,old,s);even=R[-1];spatial +=[odd,even]
   after=[1]+[sum((a+2*(Rm[j] if j<len(Rm) else 0))==v for j,a in enumerate(R)) for v in range(4)]
  assert not odd and not even
  assert before==e['before_features'] and after==e['after_features'] and 1-free[-1]==e['zero_reward']
  assert sum(v<<j for j,v in enumerate(free[-7:-1]))==e['phase_before']
  assert sum(v<<j for j,v in enumerate(free[-6:]))==e['phase_after']
  left={p:v for p,v in enumerate(spatial,1)}
  for t in range(2*N):
   assert left[1]==(1 if t%2==0 else free[t//2])
   old={**left,0:0};left={p:truth(old.get(p+1,0),old.get(p,0),old.get(p-1,0)) for p in range(1,max(left)+2)}
  out.append({**e,'right_truth_table_and_scalar_left_reconstruction_passed':True,'physical_left_re_evolution_passed':True})
 weights=d['certificate']['integer_multipliers'];phases=d['phase_order'];cols=[0]*(5*len(phases));reward=0
 for w,e in zip(weights,out):
  reward+=w*e['zero_reward']
  for j in range(5):cols[5*phases.index(e['phase_after'])+j]+=w*e['after_features'][j];cols[5*phases.index(e['phase_before'])+j]-=w*e['before_features'][j]
 assert min(cols)>=0 and reward==55 and cols==d['certificate']['aggregate_feature_delta']
 save('bothzero-linear-obstruction-validation.json',{'independent_examples':out,'integer_multipliers':weights,'aggregate_feature_delta':cols,'aggregate_zero_reward':reward,'all_passed':True,'actual_evolution_equivalence_formalized':False,'full_problem_solved':False})
 print({'five_examples_independently_reconstructed':True,'integer_certificate_passed':True},flush=True)
if __name__=='__main__':main()
