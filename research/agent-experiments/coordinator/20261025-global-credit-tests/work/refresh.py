from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import datetime as dt,hashlib,json,urllib.request
root=Path(__file__).resolve().parent
old=json.loads((root.parent/'counter-compatibility-20261025T1430/submissions.json').read_text())
urls={'environment':'https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/environment',
      'submissions':'https://www.wolframcloud.com/obj/rule-30-prize/Agents/submissions.json'}
def fetch(pair):
    name,url=pair;raw=urllib.request.urlopen(url,timeout=45).read()
    (root/(name+'.json')).write_bytes(raw)
    return name,json.loads(raw),hashlib.sha256(raw).hexdigest()
with ThreadPoolExecutor(max_workers=2) as pool:records=list(pool.map(fetch,urls.items()))
data={name:d for name,d,_ in records};known={e['id'] for e in old['entries']}
out={'created_utc':dt.datetime.now(dt.timezone.utc).isoformat(),'kit':data['environment'].get('kit'),
     'count':len(data['submissions']['entries']),'new_entries':[e for e in data['submissions']['entries'] if e['id'] not in known],
     'sha256':{name:sha for name,_,sha in records}}
(root/'refresh-result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
