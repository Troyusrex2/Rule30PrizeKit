"""Counterexample-guided trace-language refinement, an experiment not a proof.
Solver-derived exclusions remain unverified and never enter a Lean proof.
"""
from pathlib import Path
from fractions import Fraction
import hashlib,json,random,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root/'solver-deps'))
import z3
rng=random.Random(30302511);started=time.monotonic()
forbidden=['00','11111','010110','1011010'];cache={};rounds=[]

def realizable(word):
    if word in cache:return cache[word]
    n=len(word);s=z3.Solver();s.set(timeout=1000,random_seed=303025)
    row=[z3.BoolVal(True)]+[z3.Bool('r'+str(p)) for p in range(1,2*n+1)]
    for t in range(2*n-1):
        new=[z3.BoolVal((t+1)%2==0)]
        for p in range(1,len(row)-1):
            b=z3.Bool('c'+str(t+1)+'_'+str(p));new.append(b)
            s.add(b==z3.Xor(row[p-1],z3.Or(row[p],row[p+1])))
        row=new
        if t%2==0:s.add(row[1]==bool(1-int(word[t//2])))
    result=str(s.check());cache[word]=result
    return result

def cycle(prefix,first):
    mu=2*len(prefix);width=mu+4;mask=(1<<width)-1
    def f(s):return int(prefix[s]) if s<len(prefix) else first^((s-len(prefix))%2)
    cur=sum((1 if t%2==0 else f(t//2))<<t for t in range(width));prev=0;seen={};out=[]
    for _ in range(12000):
        key=(prev,cur)
        if key in seen:
            entry=seen[key];bits=out[entry:]
            return {'entry_depth':entry+1,'period':len(bits),'black':sum(bits),'cycle_bits':''.join(map(str,bits)),
                    'entry_previous_hex':hex(prev),'entry_current_hex':hex(cur)}
        seen[key]=len(out);out.append(cur&1)
        shifted=(cur>>1)|(((cur>>mu)&1)<<(width-1));prev,cur=cur,(shifted^(cur|prev))&mask
    return None

for iteration in range(20):
    candidate=None;tried=0
    if iteration==0:
        b=json.loads((root/'language-filtered-cycles.json').read_text())['best']
        candidate={'prefix_bits':b['prefix_bits'],'tail_first':b['alternating_tail_first_bit'],
                   'cycle':cycle(b['prefix_bits'],b['alternating_tail_first_bit'])}
    else:
        for sample in range(1200):
            m=[32,64,96,128][sample%4];prefix='0';maxlen=max(map(len,forbidden))
            def legal(s):return all(w not in s for w in forbidden)
            while len(prefix)<m:
                opts=[str(b) for b in [0,1] if legal(prefix[-maxlen:]+str(b))]
                if not opts:break
                prefix+=rng.choice(opts)
            if len(prefix)<m:continue
            tails=[b for b in [0,1] if legal(prefix+''.join(str(b^(j%2)) for j in range(2*maxlen+8)))]
            if not tails:continue
            first=rng.choice(tails);c=cycle(prefix,first);tried+=1
            if c and c['black']*7<2*c['period']:
                candidate={'prefix_bits':prefix,'tail_first':first,'cycle':c};break
            if time.monotonic()-started>180:break
    if candidate is None:
        rounds.append({'iteration':iteration,'samples':tried,'outcome':'no lower-density cycle found in bounded samples'});break
    prefix=candidate['prefix_bits'];queries=[];bad=None
    for n in [8,12,16,20,24,28,32]:
        r=realizable(prefix[:n]);queries.append({'prefix_length':n,'result':r})
        if r=='unsat':bad=prefix[:n];break
        if r=='unknown':break
    rec={'iteration':iteration,'samples':tried,'candidate':candidate,'prefix_queries':queries}
    if bad:
        # Shrink only by contiguous prefix/suffix deletion, with every deletion
        # independently queried against the full corresponding causal cone.
        while len(bad)>1 and realizable(bad[1:])=='unsat':bad=bad[1:]
        while len(bad)>1 and realizable(bad[:-1])=='unsat':bad=bad[:-1]
        assert all(w not in bad for w in forbidden)
        forbidden.append(bad);rec.update({'outcome':'solver-unverified new trace exclusion','word':bad})
    else:
        rec['outcome']='realizability unresolved; do not infer an actual finite-right counterexample'
    rounds.append(rec);print(json.dumps(rec),flush=True)
    if bad is None or time.monotonic()-started>180:break

out={'finite_only':True,'Lean_verified':False,'rng_seed':30302511,'z3_version':z3.get_version_string(),
     'rounds':rounds,'heuristic_forbidden_words':forbidden,'solver_queries':cache,
     'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'CEGAR tests whether nonphysical traces defeat the proposed density bound. No inferred word is kernel-checked; no actual infinite finite-R trace or unbounded positive result is established.'}
(root/'coupled-language-cegar.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
