from pathlib import Path
import json
r=Path(__file__).resolve().parent
j=json.loads((r/'extension-audit.json').read_bytes());assert j['passed']
def symbol(z):return '('+str(bool(z>>1)).lower()+','+str(bool(z&1)).lower()+')'
def literal(states):return '['+','.join('⟨'+str(q[0])+','+','.join(symbol(x) for x in q[1:])+'⟩' for q in states)+']'
chunks=[j['states'][i:i+50] for i in range(0,len(j['states']),50)]
defs='\n'.join(f'def dpart{i} : List Deep := '+literal(chunk) for i,chunk in enumerate(chunks))
defs+='\ndef deepAllowed : List Deep := '+' ++ '.join('dpart'+str(i) for i in range(len(chunks)))+'\n'
checks=''
for prefix,test in [('dclosed','closedTest'),('good','goodTest')]:
    for i in range(len(chunks)):
        checks+=f'theorem {prefix}{i} : dpart{i}.all {test}=true := by decide +kernel\n'
    checks+=f'theorem {prefix}_check : deepAllowed.all {test}=true := by\n  simp only [deepAllowed,List.all_append,'+','.join(prefix+str(i) for i in range(len(chunks)))+',Bool.true_and]\n'
s=(r/'observer_reduction_template.lean').read_text(encoding='utf-8').replace('EXTENSION_DEFS',defs).replace('EXTENSION_CHECKS',checks)
(r/'Rule30ReaderObserverReductionResearch.lean').write_text(s,encoding='utf-8')
p=r/'replay.py';s=p.read_text(encoding='utf-8')
if "HEADS['Rule30ReaderObserverReductionResearch']" not in s:
    s=s.replace('assert module in HEADS',"HEADS['Rule30ReaderObserverReductionResearch']=['extension_words','same_snoc']\nassert module in HEADS")
p.write_text(s,encoding='utf-8')
s=p.read_text(encoding='utf-8').replace("['extension_words','same_snoc']", "['extension_words','same_snoc','parent_observer_iff','parent_bit_complete_reduction']")
p.write_text(s,encoding='utf-8')
