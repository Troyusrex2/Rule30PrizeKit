"""Bounded integer synthesis of a richer prefix-peak simulation game.

The witness input prefix may continue after the adversary chooses an output
prefix, then stop and hold its score. It may also stop early if a reader
potential bounds every future output-prefix gain. This retains unbounded
input prefixes without requiring a fixed prefix lag. SAT certificates are
independently checked with Python integer arithmetic; no Lean rank is claimed.
"""
import argparse,hashlib,json,sys,time
from pathlib import Path
import numpy as np
from core import BASE,HERE,save
sys.path.insert(0,str(BASE/'toolchain/python-research'))
import z3
from universal_folded_row_rank import graph,updated
from universal_folded_prefix_peak_lagged import post_states,suffix_paths,transient

def problem_graph(T,toy):
 if toy=='delete':
  return [(0,(),0,0),(1,(3,),0,0),(3,(3,1),0,0)],[(0,1,0,3,[]),(1,2,0,1,[(0,3)])],{2:(0,0,[])},{0,1,2}
 if toy=='identity':
  return [(0,(),0,0),(3,(3,),0,0),(3,(3,1),0,0)],[(0,1,0,3,[(0,3)]),(1,2,0,1,[(0,1)])],{2:(0,0,[])},{0,1,2}
 return graph(T)

def verify(T,data,certificate):
 states,edges,terminals,live=data;C=certificate['cost'];H=certificate['future_bound'];B=certificate['bounded_reader'];Z0=dict(certificate['active_potentials']);Z1=dict(certificate['stopped_potentials']);bound=certificate['weight_bound'];pot=certificate['potential_bound'];post=post_states(T)
 assert C[0][3]>=1 and all(-bound<=v<=bound for row in C for v in row)
 assert all(0<=v<=pot for v in H) and all(-pot<=v<=pot for v in list(Z0.values())+list(Z1.values())) and Z0[0]==0
 for q in range(len(T)):
  if B[q]:
   for a in range(4):assert B[int(T[q,a])] and H[q]>=C[q][a]+H[int(T[q,a])]
 for u,v,p,x,emitted in edges:
  a=C[p][x];b=sum(C[q][y] for q,y in emitted);q=states[v][3];d=Z0[u]+b
  assert d-a<=Z0[v] or (B[q] and d-a+H[q]<=-1) or (B[q] and d+H[q]<=-1)
  if emitted:assert d-a<=Z1[v] or d-a<=-1 or d<=-1
  assert Z1[u]-a<=Z1[v] or Z1[u]-a<=-1 or Z1[u]<=-1
 for u,(p,r,tail) in terminals.items():
  previous=suffix_paths(T,p,states[u][1],1,post)
  for path in previous:
   pp,x=path[0];assert Z1[u]<=-1 or Z1[u]+C[pp][x]<=-1
  partial=0
  for emitted in [None]+list(tail):
   if emitted is not None:q,y=emitted;partial+=C[q][y]
   for path in previous:
    pp,x=path[0];assert Z0[u]+partial<=-1 or Z0[u]+partial+C[pp][x]<=-1
 return {'integer_costs_and_all_game_inequalities_checked':True,'graph_edges_checked':len(edges),'terminal_states_checked':len(terminals)}

def synth(T,toy=None,seconds=30,weight_bound=8,potential_bound=256):
 start=time.monotonic();data=problem_graph(T,toy);states,edges,terminals,live=data;post=post_states(T)
 solver=z3.Solver();solver.set(timeout=int(seconds*1000),max_memory=1536,random_seed=302555)
 C=[[z3.Int(f'C_{p}_{a}') for a in range(4)] for p in range(len(T))];H=[z3.Int(f'H_{p}') for p in range(len(T))];B=[z3.Bool(f'B_{p}') for p in range(len(T))]
 Z0={u:z3.Int(f'Z0_{u}') for u in live};Z1={u:z3.Int(f'Z1_{u}') for u in live}
 for row in C:
  for c in row:solver.add(-weight_bound<=c,c<=weight_bound)
 for h in H:solver.add(0<=h,h<=potential_bound)
 for z in list(Z0.values())+list(Z1.values()):solver.add(-potential_bound<=z,z<=potential_bound)
 solver.add(C[0][3]>=1,Z0[0]==0)
 for q in range(len(T)):
  for a in range(4):solver.add(z3.Implies(B[q],z3.And(B[int(T[q,a])],H[q]>=C[q][a]+H[int(T[q,a])])))
 for u,v,p,x,emitted in edges:
  a=C[p][x];b=sum((C[q][y] for q,y in emitted),z3.IntVal(0));q=states[v][3];d=Z0[u]+b
  solver.add(z3.Or(d-a<=Z0[v],z3.And(B[q],d-a+H[q]<=-1),z3.And(B[q],d+H[q]<=-1)))
  if emitted:solver.add(z3.Or(d-a<=Z1[v],d-a<=-1,d<=-1))
  solver.add(z3.Or(Z1[u]-a<=Z1[v],Z1[u]-a<=-1,Z1[u]<=-1))
 for u,(p,r,tail) in terminals.items():
  previous=suffix_paths(T,p,states[u][1],1,post)
  for path in previous:
   pp,x=path[0];solver.add(z3.Or(Z1[u]<=-1,Z1[u]+C[pp][x]<=-1))
  partial=z3.IntVal(0)
  for emitted in [None]+list(tail):
   if emitted is not None:q,y=emitted;partial=partial+C[q][y]
   for path in previous:
    pp,x=path[0];solver.add(z3.Or(Z0[u]+partial<=-1,Z0[u]+partial+C[pp][x]<=-1))
 status=solver.check();rec={'reader_states':len(T),'live_states':len(live),'edges':len(edges),'assertions':len(solver.assertions()),'integer_weight_bound':weight_bound,'potential_bound':potential_bound,'smt_status':str(status),'toy':toy,'z3_version':z3.get_version_string(),'seconds':round(time.monotonic()-start,3),'simulation_is_sufficient_not_complete':True}
 if status==z3.unknown:rec['reason_unknown']=solver.reason_unknown()
 if status==z3.sat:
  m=solver.model();value=lambda x:m.eval(x,model_completion=True).as_long()
  cert={'cost':[[value(c) for c in row] for row in C],'future_bound':[value(h) for h in H],'bounded_reader':[z3.is_true(m.eval(b,model_completion=True)) for b in B],'active_potentials':[[u,value(Z0[u])] for u in sorted(live)],'stopped_potentials':[[u,value(Z1[u])] for u in sorted(live)],'weight_bound':weight_bound,'potential_bound':potential_bound}
  rec['independent_check']=verify(T,data,cert);rec['certificate']=cert;rec['transition_table']=T.tolist();rec['exact_integer_game_certificate']=True
 return rec

def models():
 yield 'constant_post',np.ones((2,4),dtype=np.int16)
 for plane in [1,2,3]:
  base=np.array([[0 if x&plane==plane else 1 for x in range(4)],[1]*4],dtype=np.int16)
  yield 'black_prefix_plane'+str(plane),transient(base)
 row=[int((p+1)%7==0) for p in range(7)]
 for phase in range(4):
  if row[0]:
   pattern=[row[(-d)%7]+2*row[d%7] for d in range(1,8)];T=np.full((9,4),8,dtype=np.int16);T[0,:]=1
   for j,x in enumerate(pattern):T[1+j,x]=1+(j+1)%7
   yield 'c7_prefix_phase'+str(phase),T
  row=[(30>>((row[(p-1)%7]<<2)|(row[p]<<1)|row[(p+1)%7]))&1 for p in range(7)]

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=30);p.add_argument('--total-seconds',type=float,default=165);a=p.parse_args();start=time.monotonic();T=np.zeros((1,4),dtype=np.int16)
 pos=synth(T,'delete',5);neg=synth(T,'identity',5);assert pos.get('exact_integer_game_certificate') and neg['smt_status']=='unsat'
 save('folded-peak-game-controls.json',{'toy_deletion_positive':pos,'toy_identity_negative':neg,'all_passed':True,'Lean_verified':False,'full_problem_solved':False})
 out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'graph_source_sha256':hashlib.sha256((HERE/'universal_folded_row_rank.py').read_bytes()).hexdigest(),'records':[],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 for kind,T in models():
  r=synth(T,seconds=a.seconds);r['kind']=kind;out['records'].append(r);out['seconds']=round(time.monotonic()-start,3);save('folded-peak-game.json',out);print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
  if r.get('exact_integer_game_certificate') or time.monotonic()-start>a.total_seconds:return
if __name__=='__main__':main()
