from image_core import *
f=[int(s==6)^(s%2) for s in range(18)]
records=[];found=[]
for n in range(6,13):
    for start in range(len(f)-n+1):
        w=f[start:start+n]
        if any(r['free_bits']==''.join(map(str,w)) for r in records):continue
        r=solve(w);r['start']=start;r['free_bits']=''.join(map(str,w));records.append(r)
        if r['status']=='unsat':found.append(r)
    if found:break
out={'tested':records,'shortest_detected_exclusions':found,'Lean_verified':False,'finite_only':True}
(ROOT/'minimal-word.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'tested':len(records),'shortest_detected_exclusions':found}),flush=True)
