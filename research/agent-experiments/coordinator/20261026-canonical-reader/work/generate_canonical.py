from pathlib import Path
import json
r=Path(__file__).resolve().parent
j=json.loads((r/'canonical-audit.json').read_bytes())
assert all(j[k]['complete'] and j[k]['counterexample'] is None for k in ['coverage','unique','time_invariance'])
def lean(x):
    if isinstance(x,bool):return str(x).lower()
    if isinstance(x,int):return str(x)
    return '['+','.join(lean(v) for v in x)+']'
def pair(x):return '('+','.join(lean(v) for v in x)+')'
s=(r/'canonical_template.lean').read_text(encoding='utf-8')
s=s.replace('COVER_STATES','['+','.join('['+','.join(pair(v) for v in S)+']' for S in j['coverage']['states'])+']')
s=s.replace('COVER_EDGES',lean(j['coverage']['edges']))
s=s.replace('UNIQUE_STATES','['+','.join('⟨'+','.join(lean(v) for v in S)+'⟩' for S in j['unique']['states'])+']')
s=s.replace('TIME_STATES','['+','.join('⟨'+','.join(lean(bool(v)) if i>=2 else lean(v) for i,v in enumerate(S))+'⟩' for S in j['time_invariance']['states'])+']')
(r/'Rule30ReaderCanonicalResearch.lean').write_text(s,encoding='utf-8')
p=r/'replay.py';s=p.read_text(encoding='utf-8')
if "HEADS['Rule30ReaderCanonicalResearch']" not in s:
    s=s.replace('assert module in HEADS',"HEADS['Rule30ReaderCanonicalResearch']=['canonical_exists','canonical_unique','canonical_step']\nassert module in HEADS")
    p.write_text(s,encoding='utf-8')
s=p.read_text(encoding='utf-8')
s=s.replace("HEADS['Rule30ReaderCanonicalResearch']=['canonical_exists','canonical_unique','canonical_step']", "HEADS['Rule30ReaderCanonicalResearch']=['canonical_exists','canonical_unique','canonical_step','same_iff_normal_eq','normal_step','canonical_completeness_reduction','canonical_count']")
p.write_text(s,encoding='utf-8')
print('Generated canonical existence, uniqueness, and update-invariance certificates')
