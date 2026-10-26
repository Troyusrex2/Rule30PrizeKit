from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
manifest=json.loads((root/'manifest.json').read_bytes())
for name,digest in manifest['files'].items():
    path=(root/name).resolve();assert path.is_relative_to(root)
    assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,name
assert hashlib.sha256((root/'RootEventHeight.lean').read_bytes()).hexdigest()=='c3e092489185d6f38bf3313c027776b90e66b1485c431c2ab9e1ee33ed8248b4'
for module,count,heads in [('RootEventHeight',43,3),('RootAntiPeriodHeight',26,6)]:
    raw=(root/(module+'.lean')).read_bytes()
    report=json.loads((root/'formal'/module/'report.json').read_bytes());c=report['checker']
    assert report['passed'] and report['source_sha256']==hashlib.sha256(raw).hexdigest()
    assert report['pin']=='5473ffd075f63c9d626e63b8455805d4831b39ca'
    assert report['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True}
    assert not c['newAxioms'] and not c['verifiedTargets'] and c['importsStatements'] and c['claim']=='partial'
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',raw,re.M)
    g=json.loads((root/'evidence'/('replay-'+module+'.guard.json')).read_bytes())
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
print(json.dumps({'passed':True,'file_hashes':len(manifest['files']),'new_declarations':26,'dependency_declarations':43,'A2_necessary_condition_verified':True,'D3_or_ancestry_claim':False}))
