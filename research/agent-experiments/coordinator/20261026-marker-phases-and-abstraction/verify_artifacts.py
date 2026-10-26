from pathlib import Path
import hashlib,json,re
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
for item in s['prior_root_dependencies']:
 name=item['module'];r=json.loads((root/'prior-dependencies'/name/'report.json').read_bytes())
 assert sha(root/'sources'/(name+'.lean'))==item['source_sha256']==r['source_sha256']
 assert r['compiled_sha256']==item['compiled_sha256']
 assert r['checker']['verdict']=='pass' and r['checker']['replay']['ok'] and not r['checker']['newAxioms']
assert len(s['prior_root_dependencies'])==13
assert sum(x['declarations'] for x in s['prior_root_dependencies'])==656
assert sum(x['declarations'] for x in s['root_fresh_replays'])==238
order='CedarSafetySoundness CedarSafetySemantics CedarSafetyBridge CedarWhiteTransport RootShortExtensionCore RootEventHeight CedarNo11011 HeightOneLogic HeightOneSemantics HeightTwoNearReturn HeightTwoDescent HeightTwoMixedControl CedarMarkerReturnTwo AnchoredDefectAbstraction MarkerCarryAmbiguity MarkerCarryReconstruction MarkerCarryProjectedCycle MarkerTailStructure'.split()
names={p.stem for p in (root/'sources').glob('*.lean')};assert names==set(order)
seen=set()
for name in order:
 raw=(root/'sources'/(name+'.lean')).read_bytes()
 for imported in re.findall(rb'^import\s+(\S+)',raw,re.M):
  imp=imported.decode()
  assert imp not in names or imp in seen,(name,imp)
 seen.add(name)
print(json.dumps({'passed':True,'artifact_hashes':len(files),'fresh_modules':5,'fresh_replayed_declarations':238,'prior_dependencies':13,'import_order_checked':True,'prize_solved':False}))
