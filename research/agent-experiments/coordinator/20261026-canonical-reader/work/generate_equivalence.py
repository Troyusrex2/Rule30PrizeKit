from pathlib import Path
import json
r=Path(__file__).resolve().parent
d=json.loads((r/'reader-equivalence-audit.json').read_bytes())
assert all(d[k]['passed'] for k in ['reflexive','symmetric','transitive'])
def literal(xs):return '['+','.join('('+','.join(map(str,x))+')' for x in xs)+']'
s=(r/'reader_equivalence_template.lean').read_text(encoding='utf-8')
s=s.replace('__TRIPLES__',literal(d['transitive']['states'])).replace('__PAIRS__',literal(d['symmetric']['states']))
(r/'Rule30ReaderEquivalenceResearch.lean').write_text(s,encoding='utf-8')
print(json.dumps({'transitivity_states':len(d['transitive']['states']),'symmetry_states':len(d['symmetric']['states'])}))
