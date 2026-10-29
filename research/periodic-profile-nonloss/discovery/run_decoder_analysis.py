from pathlib import Path
import json,collections
ROOT=Path(__file__).resolve().parent
g=json.loads((ROOT/'attempt01-g913/RESULTS.json').read_text())['graphs'][-1]
groups=collections.defaultdict(set);both={tuple(p) for p in g['nodes']};complement=True;deriv=collections.defaultdict(set);mask=(1<<32)-1
for a,b in g['nodes']:
    complement=complement and (a,b^mask) in both
    d=b^((b>>1)|((b&1)<<31));deriv[d].add(a)
    for t in range(32):
        if (d>>t)&1:continue
        length=0
        while ((d>>((t+1+length)%32))&1) and length<32:length+=1
        groups[length].add(tuple((a>>((t+j)%32))&1 for j in range(length+2)))
out=dict(complement_closed=complement,derivative_nonunique=[dict(d=d,older=sorted(v)) for d,v in deriv.items() if len(v)>1],run_decoder_counts={k:len(v) for k,v in sorted(groups.items())},run_conflicts={k:[list(w) for w in sorted(v)][:3] for k,v in groups.items() if len(v)>1})
(ROOT/'RUN-DECODER-ANALYSIS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
