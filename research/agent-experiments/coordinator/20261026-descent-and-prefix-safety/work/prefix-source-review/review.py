from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
base=root.parent/'returning-prefix-safety-20261026T2029'
meta=json.loads((base/'sources.json').read_text())
results=[]
for name in ['RootReturningPrefixSafety','RootMinimalCounterexample']:
    sha=hashlib.sha256((base/(name+'.lean')).read_bytes()).hexdigest()
    report=json.loads((root/'receipts'/(name+'.json')).read_text())
    assert sha==meta['sources'][name]==report['source_sha256']
    check=report['checker']
    assert check['verdict']=='pass' and check['replay']['ok'] and not check['newAxioms']
    assert all(h['ok'] for h in check['headlines'])
    assert report['pin']=='5473ffd075f63c9d626e63b8455805d4831b39ca'
    assert report['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    results.append({'module':name,'source_sha256':sha,'replayed_declarations':check['replay']['constants']})
for name,d in meta['dependencies'].items():
    p=root.parent/d['phase']/(name+'.lean')
    assert hashlib.sha256(p.read_bytes()).hexdigest()==d['source_sha256'],name
(root/'RECEIPTS.json').write_text(json.dumps({'hashes_pass':True,'dependent_sources_checked':len(meta['dependencies']),'modules':results},indent=2)+'\n')
print(json.dumps(results))
