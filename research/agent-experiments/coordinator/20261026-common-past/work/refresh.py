from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
import hashlib,json,urllib.request
ROOT=Path(__file__).resolve().parent
old=ROOT.parent/'round3-evaluation-20261026T0103'
urls={'environment':'https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/environment',
      'submissions':'https://www.wolframcloud.com/obj/rule-30-prize/Agents/submissions.json',
      'skill':'https://www.wolframcloud.com/obj/rule-30-prize/Agents/skill.md'}
def get(k):return k,urllib.request.urlopen(urls[k],timeout=40).read()
with ThreadPoolExecutor(max_workers=3) as pool:raw=dict(pool.map(get,urls))
for k,b in raw.items():(ROOT/(k+('.md' if k=='skill' else '.json'))).write_bytes(b)
env=json.loads(raw['environment']);subs=json.loads(raw['submissions'])
before={r['id']:r for r in json.loads((old/'submissions.json').read_bytes())['entries']}
after={r['id']:r for r in subs['entries']}
out={'utc':datetime.now(timezone.utc).isoformat(),'kit':env.get('kit'),'entries':len(after),
     'new_ids':sorted(after.keys()-before.keys()),'changed_ids':sorted(k for k in before.keys()&after.keys() if before[k]!=after[k]),
     'removed_ids':sorted(before.keys()-after.keys()),'skill_changed':raw['skill']!=(old/'skill.md').read_bytes(),
     'sha256':{k:hashlib.sha256(b).hexdigest() for k,b in raw.items()}}
(ROOT/'refresh-result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
