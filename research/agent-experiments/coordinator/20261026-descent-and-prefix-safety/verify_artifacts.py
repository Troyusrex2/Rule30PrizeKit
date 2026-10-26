from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=json.loads((root/'artifacts.json').read_bytes())['files']
for name,h in files.items():
    p=(root/name).resolve()
    assert p.is_relative_to(root) and sha(p)==h,name
s=json.loads((root/'summary.json').read_bytes())
for item in s['root_fresh_replays']:
    name=item['module'];r=json.loads((root/'formal'/name/'report.json').read_bytes())
    c=r['checker'];g=json.loads((root/'evidence'/('replay-'+name+'.guard.json')).read_bytes())
    assert sha(root/'sources'/(name+'.lean'))==r['source_sha256']==item['source_sha256']
    assert r['pin']==s['pin'] and r['checker_sha256']==s['checker_sha256']
    assert c['verdict']=='pass' and c['replay']=={'constants':item['declarations'],'ok':True}
    assert not c['newAxioms'] and not c['verifiedTargets']
    assert all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
assert sum(x['declarations'] for x in s['root_fresh_replays'])==398
print(json.dumps({'passed':True,'artifact_hashes':len(files),'fresh_modules':9,'fresh_replayed_declarations':398,'prize_solved':False}))
