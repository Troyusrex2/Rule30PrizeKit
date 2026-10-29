from pathlib import Path
import json,time
ROOT=Path(__file__).resolve().parent
def rule(l,c,r):return l^(c|r)
def output_pair(w):
    x=[(w>>j)&1 for j in range(6)]
    y=[rule(*x[j:j+3]) for j in range(4)]
    return rule(*y[:3])+2*rule(*y[1:])
start=time.monotonic();records=[]
for h in range(16):
    seen={};conflict=None
    for w in range(64):
        if time.monotonic()-start>10:raise TimeoutError('fixed factor cap')
        project=lambda pair:(h>>pair)&1
        triple=tuple(project((w>>(2*j))&3) for j in range(3))
        value=project(output_pair(w))
        if triple in seen and seen[triple][1]!=value:
            conflict={'first':seen[triple][0],'second':w,'projected_triple':list(triple),
                      'first_output':seen[triple][1],'second_output':value}
            break
        seen[triple]=(w,value)
    records.append({'map':h,'constant':h in [0,15],'factor':conflict is None,'conflict':conflict})
out={'status':'nonconstant_factor_found' if any(r['factor'] and not r['constant'] for r in records) else 'no_nonconstant_two_cell_binary_factor',
     'records':records,'seconds':time.monotonic()-start,'scope':'Exact finite exhaustive computation, not Lean'}
(ROOT/'block-factor-result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],'maps',len(records),'seconds',out['seconds'])
