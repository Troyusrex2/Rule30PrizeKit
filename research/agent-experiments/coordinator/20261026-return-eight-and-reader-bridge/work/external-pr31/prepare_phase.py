"""Freeze exact public PR sources and the immutable official import graph."""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parent
repo=Path('D:/MWB/Rule30/overnight-20261024')
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
new={'Ruliology.CellularAutomata.Rule30WhiteEndNine':root/'Rule30WhiteEndNine.lean',
     'Ruliology.CellularAutomata.Rule30PaddedWords':root/'Rule30PaddedWords.lean'}
blobs={'Rule30WhiteEndNine.lean':'343b3e06b5bea7a2fdebaedbdcd50e21552efb6d',
       'Rule30PaddedWords.lean':'7c0cce3d8bcf93fc20c452773b935bb96241236a'}
official={}
def imports(raw):
    return re.findall(r'^(?:public )?import\s+([\w.]+)',raw.decode('utf-8'),re.M)
def visit(module):
    if module in new or module in official or not module.startswith('Ruliology.'):
        return
    path='lean/'+module.replace('.','/')+'.lean'
    raw=subprocess.check_output(['git','-C',str(repo),'show',pin+':'+path])
    official[module]={'path':path,'source_sha256':hashlib.sha256(raw).hexdigest()}
    for dependency in imports(raw):visit(dependency)
for source in new.values():
    raw=source.read_bytes()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[source.name]
    for dependency in imports(raw):visit(dependency)
(root/'official-dependencies.json').write_text(json.dumps({'pin':pin,'modules':official},indent=2)+'\n',encoding='utf-8')
sources={'upstream_repository':'AIOvernight/Rule30PrizeKit','upstream_commit':'88dd51194cc4ae48bff5339418d33b54265330cb','pr':'https://github.com/WolframInstitute/Rule30PrizeKit/pull/31','sources':{m:{'local_file':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'git_blob_sha1':blobs[p.name],'byte_count':p.stat().st_size,'imports':imports(p.read_bytes())} for m,p in new.items()},'official_pin':pin,'fetch_method':'GitHub connector github_fetch_file with exact commit ref, base64 decoded without text normalization'}
(root/'public-source.json').write_text(json.dumps(sources,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'pinned_official_modules':len(official),'exact_public_sources':len(new),'git_blob_hashes_match':True}))
