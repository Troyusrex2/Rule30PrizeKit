"""Versioned strip search with the full conditional width-six language.

Generate a new helper without modifying any previously hashed source.
An Aho-style suffix state retains exactly the context needed to reject
each forbidden word. Eventual constraints are usable because the strip
model already permits additive initial slack. No CA bridge is claimed.
"""
import hashlib,itertools,time
from pathlib import Path
import numpy as np
from core import save

FORBIDDEN_U=['11','00000','100101','10010001','101001','1010100001','1010001001','10010000101','1001000010001']
ORIGINAL_FREE=['00','11111','010110','1011010']
FORBIDDEN=sorted(set(ORIGINAL_FREE+[''.join(str(1-int(c)) for c in w) for w in FORBIDDEN_U]),key=lambda w:(len(w),w))

def prepare():
 source=Path('universal_strip_energy.py').read_text(encoding='utf-8')
 start=source.index('FORBIDDEN=');end=source.index('def successors',start)
 block='FORBIDDEN='+repr([tuple(map(int,w)) for w in FORBIDDEN])+'\n'
 block+='PREFIXES={w[:i] for w in FORBIDDEN for i in range(len(w))}\n'
 block+='def legal(ctx):return all(ctx[-len(w):]!=w for w in FORBIDDEN)\n'
 block+='def context(word):return max((p for p in PREFIXES if not p or word[-len(p):]==p),key=len)\n'
 result=source[:start]+block+source[end:]
 assert result.count('word[-6:]')==1
 result=result.replace('word[-6:]','context(word)')
 target=Path('universal_strip_bad_language_energy.py');target.write_text(result,encoding='utf-8',newline='\n')
 return target

def main():
 target=prepare();import universal_strip_bad_language_energy as helper
 words=[()];checks=0
 for n in range(19):
  for word in words:
   ctx=helper.context(word)
   assert len(ctx)<=12
   for x in range(2):
    expected=all(tuple(map(int,w)) not in [word[i:i+len(w)] for i in range(len(word)+1-len(w))] for w in FORBIDDEN)
    assert expected
    assert helper.legal(ctx+(x,))==all((word+(x,))[-len(w):]!=tuple(map(int,w)) for w in FORBIDDEN)
    checks+=1
  words=[w+(x,) for w in words for x in range(2) if helper.legal(helper.context(w)+(x,))]
 save('bad-language-strip-controls.json',{'forbidden_free_words':FORBIDDEN,'suffix_automaton_states':len(helper.PREFIXES),'independent_language_extension_checks':checks,'all_passed':True,'Lean_verified':False});print({'controls':checks,'suffix_states':len(helper.PREFIXES)},flush=True)
 from universal_strip_structured import readers
 start=time.monotonic();out={'generated_helper_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'domain':'eventual complete width-six free-word exclusions plus unconditional guards','additive_slack_allowed':True,'records':[],'Lean_verified':False,'CQ01_proved':False,'full_problem_solved':False}
 for M in range(3,8):
  graphs=[('constant',np.zeros((1,1<<M),dtype=np.int16))]+list(readers(M))[:6]
  for kind,T in graphs:
   begin=time.monotonic();r=helper.synth(M,T,seconds=15);r.update({'kind':kind,'seconds':round(time.monotonic()-begin,3)})
   if not r.get('useful_critical_candidate'):r.pop('certificate',None)
   out['records'].append(r);out['seconds']=round(time.monotonic()-start,3);save('bad-language-strip.json',out);print({k:v for k,v in r.items() if k not in ['certificate','transition_table']},flush=True)
   if r.get('useful_critical_candidate') or time.monotonic()-start>180:return
if __name__=='__main__':main()
