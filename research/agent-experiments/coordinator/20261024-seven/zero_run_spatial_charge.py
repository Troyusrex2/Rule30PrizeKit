"""Test the stronger all-free-word charge by counting starts of zero runs."""
import random,time
from core import save
from charge_beam_packed import step,controls
from joint_spatial_charge import physical

def main():
 start=time.monotonic();rng=random.Random(302530);records=[];counter=None;cases=0
 for mode in ['all_small','random_long']:
  inputs=((w,16) for w in range(1<<16)) if mode=='all_small' else ((rng.getrandbits(n),n) for n in [128,256,512,1024]*24)
  minimum=100000
  for word,N in inputs:
   R=Rm=spatial=cost=runs=0;previous=1;free=[]
   for d in range(N):
    s=word>>d&1;free.append(s);r,old=step(R,Rm,2*d,1);o=r>>(2*d)&1;R,Rm=step(r,old,2*d+1,s);e=R>>(2*d+1)&1
    spatial|=o<<(2*d);spatial|=e<<(2*d+1);cost+=o+e;runs+=previous and not s;previous=s;score=cost-runs;minimum=min(minimum,score)
    if score<0:
     physical(spatial,free);counter={'length':d+1,'free_prefix_hex':hex(word&((1<<(d+1))-1)),'spatial_prefix_hex':hex(spatial),'zero_runs':runs,'spatial_black':cost,'physical_evolution_recheck':True};break
   cases+=1
   if counter:break
  records.append({'mode':mode,'minimum_deficit':minimum,'cases_cumulative':cases})
  if counter:break
 save('zero-run-spatial-charge.json',{'candidate':'starts of zero runs in arbitrary free word <= black spatial prefix','records':records,'counterexample':counter,'controls':controls(),'Lean_verified':False,'uniform_bound_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)})
 print({'records':records,'counterexample':counter,'seconds':round(time.monotonic()-start,3)},flush=True)
if __name__=='__main__':main()
