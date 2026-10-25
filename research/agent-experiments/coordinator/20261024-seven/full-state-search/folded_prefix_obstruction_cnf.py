"""Find an actual finite row whose good evolution extends its folded word.

This would refute every extension-monotone center-out rank on that domain,
including signed prefix maxima, even with the eventual K6 restriction.
SAT models are independently evolved by the literal Rule 30 truth table.
Finite UNSAT and timeouts say nothing about larger radii or durations.
"""
import hashlib,time
from pathlib import Path
from core import save
from coupled_charge_cnf import Circuit,solve
from universal_folded_badclass_rank import BAD,rank

def build(N,k,bad=True):
 c=Circuit();initial={j:c.fresh() for j in range(-N,N+1)};row=initial
 c.clauses+=[[initial[0]],[initial[-N],initial[N]]]
 if bad:
  for s in range(64):
   if s in BAD:continue
   c.clauses.append([-initial.get(i+1,-1) if s>>i&1 else initial.get(i+1,-1) for i in range(6)])
 for t in range(1,2*k+1):
  old=row;row={j:c.xor(old.get(j-1,-1),c.lor(old.get(j,-1),old.get(j+1,-1))) for j in range(-N-t,N+t+1)}
  c.clauses.append([row[0] if t%2==0 else -row[0]])
 for j,x in initial.items():c.equal(x,row[j])
 return c,initial,row

def verify(N,k,initial,final,model,bad):
 row={j:int(x in model) for j,x in initial.items()};start=row.copy();centers=[row[0]]
 for t in range(1,2*k+1):
  old=row;row={j:(30>>((old.get(j-1,0)<<2)|(old.get(j,0)<<1)|old.get(j+1,0)))&1 for j in range(-N-t,N+t+1)};centers.append(row[0])
 assert centers==[1-t%2 for t in range(2*k+1)]
 assert all(row[j]==int(x in model) for j,x in final.items())
 assert all(row[j]==v for j,v in start.items())
 before=[3]+[start[-d]+2*start[d] for d in range(1,N+1)]
 after=[3]+[row[-d]+2*row[d] for d in range(1,N+2*k+1)]
 assert before[-1] and after[-1] and after[:len(before)]==before
 right=sum(start.get(i+1,0)<<i for i in range(6));assert not bad or rank(1,right)==0
 return {'input_radius':N,'good_double_steps':k,'before_folded_word':before,'after_folded_word':after,'initial_bits_lsb_left':''.join(map(str,[start[j] for j in range(-N,N+1)])),'right_first_six_rank':rank(1,right),'independent_literal_truth_table_evolution_passed':True,'proper_word_extension':True,'Lean_verified':False}

def main():
 start=time.monotonic();out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'records':[],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 for k in [1,2,3,4,7,5,6,8]:
  for N in [8,12,16,24,32,48,64]:
   c,a,b=build(N,k);begin=time.monotonic();r,m,stats=solve(c,'g4',8);rec={'radius':N,'double_steps':k,'eventual_K6_rank_zero':True,'solver_status':'sat' if r is True else 'unsat' if r is False else 'unknown_timeout','seconds':round(time.monotonic()-begin,3),'variables':c.nv,'clauses':len(c.clauses),'stats':stats};out['records'].append(rec)
   if r:out['witness']=verify(N,k,a,b,m,True)
   out['seconds']=round(time.monotonic()-start,3);save('folded-prefix-obstruction-cnf.json',out);print(rec,flush=True)
   if r or time.monotonic()-start>180:return
if __name__=='__main__':main()
