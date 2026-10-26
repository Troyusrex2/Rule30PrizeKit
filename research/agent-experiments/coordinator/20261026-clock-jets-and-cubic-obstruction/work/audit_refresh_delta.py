from pathlib import Path
import json
r=Path(__file__).resolve().parent
a={v['id']:v for v in json.loads((r.parent/'or-clock-observer-20261026T0825/submissions.json').read_bytes())['entries']}
b={v['id']:v for v in json.loads((r/'submissions.json').read_bytes())['entries']}
out=[]
for k in sorted(a.keys()&b.keys()):
    if a[k]==b[k]:continue
    fields={n:{'before':a[k].get(n),'after':b[k].get(n)} for n in a[k].keys()|b[k].keys() if a[k].get(n)!=b[k].get(n)}
    out.append({'id':k,'title':b[k].get('title'),'changes':fields})
(r/'public-changes.json').write_text(json.dumps(out,indent=2,ensure_ascii=True)+'\n')
print(json.dumps(out,ensure_ascii=True))
