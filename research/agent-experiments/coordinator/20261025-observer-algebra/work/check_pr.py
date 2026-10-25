from pathlib import Path
import hashlib,json,subprocess,urllib.request
root=Path(__file__).resolve().parent
repo=Path(r'D:\MWB\Rule30\observer-barrier-catalog-20261025')
pr=json.loads(subprocess.check_output(['gh','pr','view','26','--repo','WolframInstitute/Rule30PrizeKit',
 '--json','url,state,headRefOid,body,files,reviewDecision,statusCheckRollup']))
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
assert pr['headRefOid']==head and pr['state']=='OPEN'
assert pr['body'].replace('\r\n','\n').strip()==(root/'PR-BODY.md').read_text().strip()
assert {f['path'] for f in pr['files']}=={'lean/README.md','lean/Ruliology.lean','lean/Ruliology/CellularAutomata/Rule30DividedDifference.lean'}
remote=subprocess.check_output(['git','ls-remote','fork','refs/heads/contribution/observer-barrier-20261025'],cwd=repo,text=True).split()[0]
assert remote==head
path='lean/Ruliology/CellularAutomata/Rule30DividedDifference.lean'
raw=urllib.request.urlopen('https://raw.githubusercontent.com/Troyusrex2/Rule30PrizeKit/'+head+'/'+path,timeout=45).read()
assert raw==(repo/path).read_bytes()
out={'pass':True,'head':head,'remote_head':remote,'source_sha256':hashlib.sha256(raw).hexdigest(),'PR':pr}
(root/'pr26-readback.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'pass':True,'head':head,'source_sha256':out['source_sha256'],'url':pr['url'],'state':pr['state']}))
