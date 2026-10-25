"""Falsify assigning each free zero to a new spatial black since the preceding zero."""
import random
from core import save
from charge_beam_packed import step
from empty_right_absorption import step as right_step
from joint_spatial_charge import physical

def main():
 rng=random.Random(302529);counter=None
 for q in range(100):
  initial=rng.getrandbits(128) if q else 0;xr=initial;R=Rm=spatial=0;free=[];last=None;cost_since=0
  for d in range(512):
   xr=right_step(xr,2*d);s=1^(xr&1);xr=right_step(xr,2*d+1)
   r,old=step(R,Rm,2*d,1);o=r>>(2*d)&1;R,Rm=step(r,old,2*d+1,s);e=R>>(2*d+1)&1
   spatial|=o<<(2*d);spatial|=e<<(2*d+1);free.append(s);cost_since+=o+e
   if not s:
    if last is not None and cost_since==0:
     counter={'right_initial_hex':hex(initial),'previous_free_zero':last,'next_free_zero':d,'new_spatial_ones_in_gap':0,'free_prefix':free,'spatial_prefix_hex':hex(spatial)}
     physical(spatial,free);break
    last=d;cost_since=0
  if counter:break
 save('joint-spatial-local-charge.json',{'tested_local_claim':'a new spatial black cell between every pair of free zeros','counterexample':counter,'physical_checks_passed':bool(counter),'Lean_verified':False,'full_problem_solved':False})
 print({'actual_right_counterexample_found':bool(counter),'previous':counter['previous_free_zero'],'next':counter['next_free_zero']},flush=True)
if __name__=='__main__':main()
