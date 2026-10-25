from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import datetime as dt,hashlib,json,urllib.request
root=Path(__file__).resolve().parent
old=json.loads((root.parent/'source-green-20261025T1610/submissions.json').read_text(encoding='utf-8'))
urls={'environment':'https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/environment',
      'submissions':'https://www.wolframcloud.com/obj/rule-30-prize/Agents/submissions.json'}
def fetch(pair):
    name,url=pair
    raw=urllib.request.urlopen(url,timeout=45).read()
    (root/(name+'.json')).write_bytes(raw)
    return name,json.loads(raw),hashlib.sha256(raw).hexdigest()
with ThreadPoolExecutor(max_workers=2) as pool:
    records=list(pool.map(fetch,urls.items()))
data={name:d for name,d,_ in records}
before={e['id']:e for e in old['entries']}
after={e['id']:e for e in data['submissions']['entries']}
out={'created_utc':dt.datetime.now(dt.timezone.utc).isoformat(),'kit':data['environment'].get('kit'),
     'count':len(after),'new_entries':[e for k,e in after.items() if k not in before],
     'removed_ids':sorted(set(before)-set(after)),
     'changed_entries':[{'id':k,'fields':sorted(f for f in set(before[k])|set(e) if before[k].get(f)!=e.get(f))}
                        for k,e in after.items() if k in before and before[k]!=e],
     'sha256':{name:sha for name,_,sha in records}}
(root/'refresh-result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
