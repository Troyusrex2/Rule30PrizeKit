from pathlib import Path
import hashlib,json,shutil
root=Path(__file__).resolve().parent;base=root.parent
deps=json.loads((base/'height1-transfer-20261026T2007/sources.json').read_text())['dependencies']
for phase,names in {
 'height1-transfer-20261026T2007':['HeightOneLogic','HeightOneSemantics','HeightOneTransfer','HeightOnePeriodicity'],
 'height-converse-review-20261026T1854':['RootAntiPeriodHeight'],
 'returning-prefix-safety-20261026T2029':['RootReturningPrefixSafety']}.items():
 for name in names:
  r=json.loads((base/phase/'formal'/name/'report.json').read_text())
  assert r['checker']['verdict']=='pass' and r['checker']['replay']['ok']
  deps[name]={'phase':phase,'source_sha256':r['source_sha256'],'compiled_sha256':r['compiled_sha256']}
for name,d in deps.items():
 p=base/d['phase']/(name+'.lean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==d['source_sha256']
 out=root/'dependencies';out.mkdir(exist_ok=True);shutil.copyfile(p,out/p.name)
 out=root/'dependency-receipts'/name;out.mkdir(parents=True,exist_ok=True)
 shutil.copyfile(base/d['phase']/'formal'/name/'report.json',out/'report.json')
sources={p.stem:hashlib.sha256(p.read_bytes()).hexdigest() for p in root.glob('*.lean')}
(root/'sources.json').write_text(json.dumps({'sources':sources,'dependencies':deps},indent=2)+'\n')
shutil.copyfile(base/'height1-transfer-20261026T2007/guard.py',root/'guard.py')
replay=(base/'height1-transfer-20261026T2007/replay.py').read_text()
a=replay.index('heads=');b=replay.index('\nassert module in heads',a)
replay=replay[:a]+'''heads={'SafeClockEntry':['safe_extension_preserves_even_return','safe_clock_jump_entry','safe_clock_plateau_of_not_height_two'],
       'SafeEntryLocalControl':['free_boundary_control'],
       'SafeClockDichotomy':['exists_even_whole_return','safe_last_clock_equal','safe_height_two_or_clock_plateau']}'''+replay[b:]
(root/'replay.py').write_text(replay)
print(json.dumps({'sources':sources,'dependencies':len(deps)}))
