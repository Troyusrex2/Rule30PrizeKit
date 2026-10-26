from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import json,hashlib,urllib.request,re
r=Path(__file__).resolve().parent;pin='207ebff1abeb05b812aac41c1cd425ab652394bc'
names=['RootedReturn.lean','ParityMask.lean','JenPow2.lean','LemmaB2.lean']
d=r/'external';d.mkdir(exist_ok=True)
def one(name):
    url=f'https://raw.githubusercontent.com/ghywel/placego/{pin}/tests/probes/lean/{name}'
    b=urllib.request.urlopen(url,timeout=30).read();(d/name).write_bytes(b)
    txt=b.decode('utf-8')
    return {'file':name,'url':url,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),
            'imports':[x for x in txt.splitlines() if x.startswith('import ')],
            'headline_lines':[x for x in txt.splitlines() if re.match(r'(?:theorem|lemma|def) ',x)],
            'source_red_flags':bool(re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b',txt)),
            'adopted':False,'full_kernel_replayed_here':False}
with ThreadPoolExecutor(4) as pool:out=list(pool.map(one,names))
(r/'related-source-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
