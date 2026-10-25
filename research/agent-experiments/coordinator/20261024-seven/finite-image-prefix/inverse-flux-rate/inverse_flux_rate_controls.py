"""Independent triangle, graph, boundary-language and energy controls."""
import itertools,json,random
from pathlib import Path
from fractions import Fraction as Q
from inverse_clock_flux_rate import reader,column_graph,boundary_graph,valid,emit,synth
def step(R,Rm,y):
 acc=y;out=[y]
 for i,a in enumerate(R):acc^=a|(0 if i==0 else Rm[i-1]);out.append(acc)
 return out,R

def output(word,columns):return [emit(a,b,columns) for a,b in zip(word,word[1:])]
def score(T,C,H,word):
 p=0;value=Q(0)
 for x in word:value+=C[p,x];p=int(T[p,x])
 return value+H[p],p

def controls():
 fields=language=identities=boundary=0;rng=random.Random(302630)
 for columns in [2,3]:
  T,words=reader(columns,2,clock=2);states,edges=column_graph(T,columns);lookup={(u,x):(v,p,x,q,y,black) for u,v,p,x,q,y,black in edges}
  C={(p,x):Q(rng.randrange(-9,10)) for p in range(len(T)) for x in range(1<<columns)};H=[Q(rng.randrange(-9,10)) for _ in range(len(T))]
  for n in range(5):
   for word in itertools.product(range(1<<columns),repeat=n):
    u=0;cost={m:Q(0) for m in [1,2,4]}
    for x in word:
     e=lookup.get((u,x))
     if e is None:u=-1;break
     u,p,x,q,y,black=e
     for mult in [1,2,4]:cost[mult]+=C[p,x]-(mult*C[q,y] if y is not None else 0)-2*black
    want=all(valid(a,b,columns) for a,b in zip(word,word[1:]));assert (u>=0)==want
    if want:
     aft=output(word,columns);ec,p=score(T,C,H,word);ea,q=score(T,C,H,aft)
     assert states[u][1:]==(p,q)
     for mult in [1,2,4]:
      assert cost[mult]+H[p]-mult*H[q]==ec-mult*ea-(2*(word[0]&1) if word else 0);identities+=1
    language+=1
  one=5 if columns==3 else 1
  for n in range(1,9):
   for free in itertools.product(range(2),repeat=n):
    R=[];Rm=[];initial=[]
    for t in range(2*n):
     R,Rm=step(R,Rm,1 if not t%2 else free[t//2]);initial.append(R[-1])
    word=[x for bit in free for x in [one,one*bit]];bits=[]
    while word:
     assert all(valid(a,b,columns) for a,b in zip(word,word[1:]));bits.append(word[0]&1);word=output(word,columns)
    assert bits==initial;fields+=len(bits)
  for domain in ['all','no00','golden','badclass']:
   bs,be=boundary_graph(T,columns,domain);look={(u,b//one):(v,p,a,q,b,reward) for u,v,p,a,q,b,reward in be}
   for n in range(9):
    for free in itertools.product(range(2),repeat=n):
     u=0;cost=Q(0);reward_sum=0
     for s in free:
      e=look.get((u,s))
      if e is None:u=-1;break
      u,p,a,q,b,reward=e;cost+=C[p,a]+C[q,b]-reward;reward_sum+=reward
     want=(domain=='all' or all(free[i:i+2]!=(0,0) for i in range(max(0,n-1)))) and (domain!='golden' or all(free[i:i+5]!=(1,1,1,1,1) for i in range(max(0,n-4))))
     if domain=='badclass':want=all(tuple(free[i:i+len(bad)])!=tuple(map(int,bad)) for bad in ['00','11111','010110','011010','1011010','01101110','0101011110','0101110110','01101111010','0110111101110'] for i in range(max(0,len(free)-len(bad)+1)))
     assert (u>=0)==want,(columns,domain,free)
     if want:
      w=[x for bit in free for x in [one,one*bit]];value,p=score(T,C,H,w)
      target=sum(int(not x and (not i or free[i-1])) for i,x in enumerate(free)) if domain=='all' else free.count(0)
      assert reward_sum==target and bs[u][0]==p and cost+H[p]==value-target;identities+=1
     boundary+=1
 calibrations=[]
 for columns in [2,3]:
  yes=synth(columns=columns,memory=1,domain='all',charge_all_symbols=True,seconds=10,spatial_multiplier=2)
  zero=synth(columns=columns,memory=1,domain='all',zero_boundary=True,seconds=10,spatial_multiplier=2)
  no=synth(columns=columns,memory=1,domain='all',factor=0,seconds=10,spatial_multiplier=2)
  assert yes.get('exact_rational_graph_certificate') and zero.get('exact_rational_graph_certificate') and no.get('boundary_charge_rate')==0,(yes,zero,no)
  calibrations.append({'columns':columns,'nontrivial_all_symbol_charge_exact_certificate':True,'zero_boundary_exact_certificate':True,'zero_spatial_payment_optimal_rate_zero':True})
 return {'spatial_multipliers_checked':[1,2,4],'literal_antidiagonal_vs_full_column_cells':fields,'exhaustive_column_graph_language_checks':language,'boundary_language_checks':boundary,'exact_rational_path_energy_identities':identities,'calibrations':calibrations,'all_passed':True,'Lean_verified':False}

if __name__=='__main__':
 r=controls();(Path(__file__).resolve().parent/'inverse-column-flux-controls.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print(json.dumps(r,indent=2))
