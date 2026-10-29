from pathlib import Path
import json,itertools
ROOT=Path(__file__).resolve().parent
S={8,9,16,18,33,36,66,72,132,144}
INV={}
for f,c,r in itertools.product(range(2),repeat=3):
    INV[f,c,r]=next(l for l in range(2) if ((30>>(4*l+2*c+r))&1)==f)

def literal(n,m,f,h,column):
    boundary=[v for i in range(n+m) for v in (1-(((h|(f<<n))>>i)&1),1)]
    prev=[0]*len(boundary);curr=boundary
    for k in range(1,column):
        prev,curr=curr,[INV[curr[t+1],curr[t],prev[t]] for t in range(len(curr)-1)]
    return curr

def completion(m,f):
    bits=[(f>>i)&1 for i in range(m)];seen={}
    while True:
        state=tuple(bits[-7:])
        if state in seen:
            j=seen[state];return {'prefix':bits[:j],'cycle':bits[j:]}
        seen[state]=len(bits)
        for b in (0,1):
            window=sum(v<<i for i,v in enumerate(list(state)+[b]))
            if window in S:bits.append(b);break
        else:raise AssertionError('no continuation')

out=[]
for n in (10,11,12):
    file=ROOT/f'n{n}-cap{10*n}-CERTIFICATE.json'
    if not file.exists():continue
    data=json.loads(file.read_text());witness=None
    for m,f in data['unresolved_frontier']:
        hs=[h for h in range(1<<n) if all((((h|(f<<n))>>i)&255) in S for i in range(n))]
        rows=[literal(n,m,f,h,20*n) for h in hs]
        for i in range(1,len(hs)):
            if rows[i][0]!=rows[0][0]:
                witness={'n':n,'column':20*n,'future_length':m,'future_word':f,'past_a':hs[0],'past_b':hs[i],'row_bits':[rows[0][0],rows[i][0]],'future_completion':completion(m,f),'literal_replay_passed':True,'hhom_refuted':False,'prize_refuted':False};break
        if witness:break
    result={'n':n,'bound_20n_refuted':witness is not None,'witness':witness,'kernel_verified':False};out.append(result)
(ROOT/'LINEAR-FALSIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{'n':r['n'],'bound_20n_refuted':r['bound_20n_refuted'],'completion_period':len(r['witness']['future_completion']['cycle']) if r['witness'] else None} for r in out]))
