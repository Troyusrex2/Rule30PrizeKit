from pathlib import Path
import hashlib,json
root=Path(__file__).parent
manifest=json.loads((root/'manifest.json').read_text())
for name,h in manifest['files'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h,name
expected={'PrizeSafetyBridge':100,'ResetExcursionControl':6}
for module,count in expected.items():
    r=json.loads((root/'independent-root-review'/(module+'-report.json')).read_text())
    assert r['source_sha256']==hashlib.sha256((root/(module+'.lean')).read_bytes()).hexdigest()
    assert r['pin']=='5473ffd075f63c9d626e63b8455805d4831b39ca'
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    c=r['checker'];assert c['verdict']=='pass' and c['replay']['ok'] and c['replay']['constants']==count and not c['newAxioms']
    g=json.loads((root/'independent-root-review'/(module+'-guard.json')).read_text())
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
print(json.dumps({'passed':True,'hashes':len(manifest['files']),'independent_root_replays':expected,
                  'full_sink_separation_proved':False,'fixed_center_bridge_proved':False,'problem1_proved':False}))
