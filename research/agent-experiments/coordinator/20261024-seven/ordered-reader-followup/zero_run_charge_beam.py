"""Try to falsify the all-free-word zero-run charge, without Golden guards.

The earlier random/enumeration tests do not justify a uniform claim. This
adversarial beam minimizes spatial black cells minus free zero-run starts.
It is heuristic; only a physically checked counterexample is conclusive.
"""
import argparse,hashlib,time
from pathlib import Path
from core import save
from charge_beam_packed import step,controls
from joint_spatial_charge import physical

def main():
 p=argparse.ArgumentParser();p.add_argument('--beam',type=int,default=4096);p.add_argument('--length',type=int,default=4096);p.add_argument('--seconds',type=float,default=165);a=p.parse_args()
 start=time.monotonic();checked=controls();states=[(0,0,0,0,0,0,1)];records=[];stopped='length_completed';counter=None
 # R,Rm,free word,spatial word,zero runs,black cost,previous free bit.
 for d in range(a.length):
  children=[];mask=(1<<(2*d+2))-1
  for R,Rm,w,spatial,runs,cost,previous in states:
   r,old=step(R,Rm,2*d,1);odd=(r>>(2*d))&1;base,_=step(r,old,2*d+1,0);pred=(base>>(2*d+1))&1
   for s in (0,1):
    even=pred^s
    children.append((base^(mask if s else 0),r,w|(s<<d),spatial|(odd<<(2*d))|(even<<(2*d+1)),runs+int(previous and not s),cost+odd+even,s))
  children.sort(key=lambda q:(q[5]-q[4],q[5],q[3]));states=children[:a.beam];best=states[0];score=best[5]-best[4]
  if (d+1)%64==0 or score<0:
   records.append({'length':d+1,'zero_runs':best[4],'spatial_black_count':best[5],'deficit':score,'seconds':round(time.monotonic()-start,3)});print(records[-1],flush=True)
  if score<0:stopped='counterexample';break
  if time.monotonic()-start>a.seconds:stopped='time_budget';break
 free=[best[2]>>i&1 for i in range(d+1)];physical(best[3],free)
 assert sum(int(not x and (j==0 or free[j-1])) for j,x in enumerate(free))==best[4]
 assert best[3].bit_count()==best[5]
 if score<0:
  counter={'length':len(free),'free_prefix_hex':hex(best[2]),'spatial_prefix_hex':hex(best[3]),'zero_runs':best[4],'spatial_black_count':best[5],'physical_evolution_passed':True}
 report={'target':'zero-run starts in arbitrary free prefix <= spatial black count','beam_width':a.beam,'requested_length':a.length,'completed_length':len(free),'stop_reason':stopped,'records':records,'final_deficit':score,'counterexample':counter,'controls':checked,'physical_re_evolution_steps':2*len(free),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'heuristic_only':True,'uniform_bound_proved':False,'Lean_verified':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
 save('zero-run-charge-beam.json',report);print({k:report[k] for k in ['stop_reason','completed_length','final_deficit','counterexample','seconds']},flush=True)
if __name__=='__main__':main()
