from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,urllib.request
r=Path(__file__).resolve().parent
with urllib.request.urlopen('https://www.wolframcloud.com/obj/rule-30-prize/Agents/submissions.json',timeout=40) as f:raw=f.read()
(r/'activity-public-feed.json').write_bytes(raw);d=json.loads(raw)
mine=[x for x in d['entries'] if x['authors'].split(';')[0].strip()=='Troy Lowry']
out={'utc':datetime.now(timezone.utc).isoformat(),'public_entries':len(d['entries']),
     'currently_listed_troy_entries':len(mine),'other_entries':len(d['entries'])-len(mine),
     'author_byline_groups':len({x['authors'] for x in d['entries']}),
     'troy_lean_verified':sum(x['status']=='Lean Verified' for x in mine),
     'troy_human_verified':sum('Human Verified' in x['tags'] for x in mine),
     'troy_kit_contributions':sum('Kit Contribution' in x['tags'] for x in mine),
     'raw_sha256':hashlib.sha256(raw).hexdigest()}
(r/'activity-feed-summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
