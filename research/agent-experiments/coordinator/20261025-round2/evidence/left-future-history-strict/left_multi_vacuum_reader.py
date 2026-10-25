"""Binary prefix-union reader for several exact periodic free backgrounds.

Start at the candidate set before the FIRST LEFT CELL; no center marker.
Include all temporal phases of free01,011,0111,01111. In particular, the
period-seven spatial ether from the checked charging obstruction is kept.
"""
import argparse,collections,hashlib,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from core import save
import left_zero_wall_graph as domain
from left_lookahead_defect_rank import synth
from left_lookahead_graph import controls as domain_controls,prefixes

def patterns():
 out=[]
 for necklace in [(0,1),(0,1,1),(0,1,1,1),(0,1,1,1,1)]:
  P=len(necklace);n=2*P;mask=(1<<n)-1
  for phase in range(P):
   free=list(necklace[phase:]+necklace[:phase]);A=sum((1 if t%2==0 else free[t//2])<<t for t in range(n));B=0;seen={};cols=[]
   while (A,B) not in seen:
    assert len(cols)<100000;seen[A,B]=len(cols);cols.append(A);A,B=(((A>>1)|((A&1)<<(n-1)))^(A|B))&mask,A
   mu=seen[A,B];period=len(cols)-mu
   assert (mu,period)=={2:(1,7),3:(1,84),4:(9,7),5:(1,155)}[P]
   out.append({'necklace':list(necklace),'phase':phase,'free_period':free,'transient':mu,'period':period,'left_bits':[c&1 for c in cols]})
 return out

def build():
 pats=patterns();initial=tuple((i,0) for i in range(len(pats)));states=[initial];index={initial:0};queue=collections.deque([initial]);rows=[]
 def bit(i,d):
  p=pats[i];a=p['left_bits'];mu=p['transient'];return a[d if d<len(a) else mu+(d-mu)%p['period']]
 while queue:
  state=queue.popleft();row=[]
  for x in range(2):
   new=tuple((i,pos+1 if pos+1<len(pats[i]['left_bits']) else pats[i]['transient']) for i,pos in state if pats[i]['left_bits'][pos]==x)
   if new not in index:assert len(states)<32767;index[new]=len(states);states.append(new);queue.append(new)
   row.append(index[new])
  rows.append(row)
 T=np.array(rows,dtype=np.int16);sink=index[()]
 def expected(word):
  out=[];n=len(word)
  for i,p in enumerate(pats):
   if all(bit(i,j)==x for j,x in enumerate(word)):out.append((i,n if n<len(p['left_bits']) else p['transient']+(n-p['transient'])%p['period']))
  return tuple(out)
 fields=language=0
 for i,p in enumerate(pats):
  W=256;previous=[0]*(W+1);current=[1 if t%2==0 else p['free_period'][t//2%len(p['free_period'])] for t in range(W)];spatial=[]
  while current:spatial.append(current[0]);previous,current=current,[current[j+1]^(current[j]|previous[j]) for j in range(len(current)-1)]
  assert spatial==[bit(i,j) for j in range(W)];fields+=W
  L=sum(b<<j for j,b in enumerate(spatial));L1=(L>>1)^(L|(L<<1));L2=(L1>>1)^(L1|(L1<<1));next_phase=(p['phase']+1)%len(p['free_period']);future=next(j for j,q in enumerate(pats) if q['necklace']==p['necklace'] and q['phase']==next_phase)
  assert [L2>>j&1 for j in range(W-4)]==[bit(future,j) for j in range(W-4)];fields+=W-4
  for flip in [-1,1,7,53,151]:
   state=0;word=[]
   for j in range(220):
    x=bit(i,j)^int(j==flip);word.append(x);state=int(T[state,x]);assert states[state]==expected(word);language+=1
 data=domain.graph(T);gstates,edges,terminals,live=data;lookup={(u,x):v for u,v,p,x,out in edges};traces=0
 for i in range(len(pats)):
  before=[bit(i,j) for j in range(64)]
  while not before[-1]:before.pop()
  after=domain.updated(before);assert after is not None;u=p=q=0
  for x in before:u=lookup[u,x];p=int(T[p,x])
  for x in after:q=int(T[q,x])
  assert u in terminals and gstates[u][2]==p and terminals[u][1]==q and states[p]==expected(before) and states[q]==expected(after)
  assert any(j==i for j,pos in states[p]);traces+=1
 c={'background_free_periods':[2,3,4,5],'temporal_phase_patterns':len(pats),'binary_reader_states':len(T),'initial_state_consumes_first_left_cell':True,'independent_triangular_and_physical_field_bits':fields,'independent_entire_prefix_language_checks':language,'actual_canonical_physical_reader_endpoint_traces':traces,'all_passed':True,'Lean_verified':False}
 return T,pats,states,c

def main():
 p=argparse.ArgumentParser();p.add_argument('--horizon',type=int,default=13);p.add_argument('--scale',default='1');args=p.parse_args();T,pats,states,c=build();save('multi-vacuum-reader-controls-H'+str(args.horizon)+'-scale'+args.scale.replace('/','-')+'.json',c);save('multi-vacuum-domain-controls-H'+str(args.horizon)+'-scale'+args.scale.replace('/','-')+'.json',domain_controls());print(c,flush=True)
 start=time.monotonic();r=synth(T,F(args.scale),seconds=75,lookahead=args.horizon);r['seconds']=round(time.monotonic()-start,3);out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'reader':c,'allowed_prefixes_per_context':[len(prefixes(i,args.horizon)[0]) for i in range(5)],'records':[r],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False};save('multi-vacuum-H'+str(args.horizon)+'-scale'+args.scale.replace('/','-')+'.json',out);print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
if __name__=='__main__':main()
