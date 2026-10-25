"""Collect only the completed owned budget-eight proof and its checked objects."""
import hashlib,json,subprocess,zipfile
from pathlib import Path
root=Path.home()/'Rule30-offload';control=root/'_cache/budget8-c600';ref=root/'reference';out=root/'results/budget8-c600'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((control/'batch-manifest.json').read_text(encoding='utf-8'));progress=json.loads((out/'progress.json').read_text(encoding='utf-8'))
assert len(progress['completed'])==404 and not progress['failed']
base=json.loads((root/'_cache/payload/payload-manifest.json').read_text(encoding='utf-8'))
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ref,text=True).strip()==base['kit_commit']
assert sha(ref/'Check.lean')==base['checker_sha256']
records=[];files={};objects={}
for rec in manifest['modules']:
 name=rec['module'];src=control/rec['source'];folder=out/name;r=json.loads((folder/'report.json').read_text(encoding='utf-8'))
 assert sha(src)==r['source_sha256']==manifest['files'][rec['source']]==sha(ref/(name+'.lean'))
 assert r['kit_commit']==base['kit_commit'] and r['checker_sha256']==base['checker_sha256']
 assert r['check']['verdict']=='pass' and r['check']['replay']['ok'] and not r['check']['newAxioms'] and all(h['ok'] for h in r['check']['headlines'])
 for obj,digest in r['object_hashes'].items():
  p=ref/'.lake/build/lib/lean'/obj;assert sha(p)==digest;objects[obj]=p
 files['formal/'+name+'.lean']=src
 for f in folder.iterdir():
  if f.name=='report.json':files['evidence/'+name+'/'+f.name]=f
 records.append({'module':name,'constants':r['check']['replay']['constants'],'source_sha256':r['source_sha256'],'report':'evidence/'+name+'/report.json'})
name='Rule30GoldenBudget8C600V2Research';src=root/'_cache'/(name+'.lean')
candidates=[]
for folder in (root/'results').glob('*-'+name):
 r=json.loads((folder/'report.json').read_text(encoding='utf-8'))
 if r.get('check',{}).get('verdict')=='pass':candidates.append((folder,r))
assert len(candidates)==1,candidates
folder,r=candidates[0];assert sha(src)==r['source_sha256']==sha(ref/(name+'.lean'))
assert r['check']['replay']['ok'] and not r['check']['newAxioms'] and all(h['ok'] for h in r['check']['headlines'])
files['formal/'+name+'.lean']=src
for f in folder.iterdir():
 if f.name=='report.json':files['evidence/'+name+'/'+f.name]=f
for f in (ref/'.lake/build/lib/lean').glob(name+'.olean*'):objects[f.name]=f
records.append({'module':name,'constants':r['check']['replay']['constants'],'source_sha256':r['source_sha256'],'report':'evidence/'+name+'/report.json'})
files['plan.json']=control/'plan.json'
files['original-batch-manifest.json']=control/'batch-manifest.json'
archive=root/'_cache/budget8-verified-evidence.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for name,p in sorted(files.items()):z.write(p,name)
 summary={'kit_commit':base['kit_commit'],'checker_sha256':base['checker_sha256'],'leaves':404,'certificate_complete':True,'full_problem_solved':False,
   'files':{name:sha(p) for name,p in sorted(files.items())},'modules':records,'object_hashes':{name:sha(p) for name,p in sorted(objects.items())}}
 z.writestr('collection-manifest.json',json.dumps(summary,indent=2)+'\n')
objarchive=root/'_cache/budget8-verified-objects.zip'
with zipfile.ZipFile(objarchive,'w',zipfile.ZIP_DEFLATED) as z:
 for name,p in sorted(objects.items()):z.write(p,name)
transfer={'evidence_sha256':sha(archive),'objects_sha256':sha(objarchive),'modules':len(records),'constants':sum(r['constants'] for r in records),'all_source_and_object_hashes_rechecked':True,'checker_unchanged':True,'full_problem_solved':False}
(root/'_cache/budget8-verified-transfer.json').write_text(json.dumps(transfer,indent=2)+'\n',encoding='utf-8')
print(transfer,flush=True)
