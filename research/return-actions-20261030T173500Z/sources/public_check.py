from pathlib import Path
import subprocess,json
R=Path(__file__).resolve().parent
r=subprocess.run(['gh','api','repos/WolframInstitute/Rule30PrizeKit/commits?per_page=5'],capture_output=True,text=True,encoding='utf-8',timeout=30)
assert r.returncode==0,r.stderr
commits=json.loads(r.stdout)
out=[dict(sha=c['sha'],date=c['commit']['committer']['date'],title=c['commit']['message'].splitlines()[0]) for c in commits]
(R/'PUBLIC_COMMITS.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
