"""Version the peak simulation with correctly aligned prefix matches."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
s=(ROOT/'universal_folded_prefix_peak.py').read_text(encoding='utf-8')
s=s[:s.index('def main():')]
s=s.replace('def synth(T,seconds=15,toy=False,fixed_zero=False):','def synth(T,seconds=15,toy=False,fixed_zero=False,offset=2):')
helper='''def post_states(T):
 found={int(T[0,3])};stack=list(found)
 while stack:
  p=stack.pop()
  for x in range(4):
   q=int(T[p,x])
   if q not in found:found.add(q);stack.append(q)
 return found

def suffix_paths(T,current,buffer,length,post):
 if length==0:return [[]]
 assert length<=len(buffer)
 answer=[]
 for p in sorted(post):
  state=p;path=[]
  for x in buffer[-length:]:path.append((state,x));state=int(T[state,x])
  if state==current:answer.append(path)
 assert answer
 return answer

'''
s=s.replace('def synth(T,',helper+'def synth(T,',1)
s=s.replace("labels=[];index={};rows=[];rhs=[]", "post=post_states(T);labels=[];index={};rows=[];rhs=[]")
s=s.replace("if states[u][0]==3:add([(Z(u),1),(alpha,1)])", "if states[u][0]==3:\n   for path in suffix_paths(T,states[u][2],states[u][1],2-offset,post):\n    add([(Z(u),1),(alpha,1)]+[(C(p,x),1) for p,x in path])")
s=s.replace("for q,y in tail:partial.append((C(q,y),1));add([(Z(u),1),(alpha,1)]+partial)", "for k,(q,y) in enumerate(tail,1):\n   partial.append((C(q,y),1))\n   for path in suffix_paths(T,p,states[u][1],max(0,2-k-offset),post):\n    add([(Z(u),1),(alpha,1)]+partial+[(C(pp,x),1) for pp,x in path])")
s=s.replace("'signed_prefix_peak_energy':True", "'signed_prefix_peak_energy':True,'prefix_match_offset':offset,'all_consistent_reader_preimages_checked':True")
s+='''def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=165);a=p.parse_args();start=time.monotonic();base=np.zeros((1,4),dtype=np.int16)
 pos=synth(base,toy=True);neg=[synth(base,fixed_zero=True,offset=h) for h in [0,1,2]]
 assert pos.get('exact_rational_graph_certificate') and pos['reward_rate']>.999999
 assert all(r['solver_status']==0 and abs(r['reward_rate'])<1e-8 for r in neg)
 save('folded-prefix-peak-lagged-controls.json',{'toy_deletion_positive':pos,'zero_energy_negative_offsets':neg,'all_passed':True,'Lean_verified':False,'full_problem_solved':False})
 records=[]
 for offset in [0,1,2]:
  for kind,T in readers():
   begin=time.monotonic();r=synth(transient(T),offset=offset);r.update({'kind':'transient_'+kind,'seconds':round(time.monotonic()-begin,3)});records.append(r)
   save('universal-folded-prefix-peak-lagged.json',{'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'graph_helper_sha256':hashlib.sha256((Path(__file__).resolve().parent/'universal_folded_row_rank.py').read_bytes()).hexdigest(),'records':records,'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)})
   print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
   if r.get('exact_rational_graph_certificate') or time.monotonic()-start>a.seconds:return
if __name__=='__main__':main()
'''
assert 'for path in suffix_paths' in s
(ROOT/'universal_folded_prefix_peak_lagged.py').write_text(s,encoding='utf-8',newline='\n')
print({'prepared':'universal_folded_prefix_peak_lagged.py'},flush=True)
