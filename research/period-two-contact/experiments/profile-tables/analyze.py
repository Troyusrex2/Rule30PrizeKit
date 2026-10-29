from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parent;source=ROOT/'PROFILE-GRAPH.json'
graphs=json.loads(source.read_text())['graphs'];results=[]
for g in graphs:
    q=g['q'];mask=(1<<q)-1;words={b for a,b in g['nodes']}
    def rot(w):return (w>>1)|((w&1)<<(q-1))
    alt=lambda w:all(((w>>t)&1)==((w>>((t+2)%q))&1) for t in range(q))
    no00=lambda w:((mask^w)&rot(mask^w))==0
    bad=sorted(w for w in words if no00(w) and not alt(w))
    cover_bad=[(a,b) for a,b in g['nodes'] if (a|b)==mask and not alt(b)]
    results.append({'q':q,'profiles':len(words),'no00_profiles':sum(no00(w) for w in words),'no00_nonperiod_two_counterexamples':bad[:3],'or_cover_nonperiod_two_counterexamples':cover_bad[:3]})
W=6;seed=33;mask=(1<<W)-1;w=seed;orbit=[]
for t in range(8):orbit.append(w);w=(w^((w<<1)|(w<<2)))&mask
assert w==seed
profile=sum(((s>>5)&1)<<t for t,s in enumerate(orbit));assert profile==87
assert all(((profile>>t)&1) or ((profile>>((t+1)%8))&1) for t in range(8))
assert any(((profile>>t)&1)!=((profile>>((t+2)%8))&1) for t in range(8))
cells={0,-5};literal=[]
for t in range(8):
    literal.append(int(t-5 in cells))
    cells={p for p in range(-6-t,2+t) if (30>>(4*int(p-1 in cells)+2*int(p in cells)+int(p+1 in cells)))&1}
assert sum(b<<t for t,b in enumerate(literal))==profile
out={'scope':'bounded table analysis only, not an unbounded theorem','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'results':results,'no00_shortcut_counterexample':{'seed':seed,'black_positions':[0,-5],'diagonal':5,'whole_prefix_cycle':8,'whole_prefix_orbit':orbit,'profile_word_little_endian':profile,'no00_circularly':True,'not_period_two':True,'ordinary_literal_rule30_replay_matches':True,'scope':'numerical exact finite-cycle witness, not a new Lean certificate'}}
(ROOT/'RESULTS.json').write_bytes((json.dumps(out,indent=2)+'\n').encode());print(json.dumps(out))
